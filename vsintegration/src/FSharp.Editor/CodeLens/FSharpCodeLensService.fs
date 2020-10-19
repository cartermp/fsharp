// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

namespace Microsoft.VisualStudio.FSharp.Editor

open System
open System.Threading
open System.Windows
open System.Windows.Controls
open System.Windows.Media
open System.Windows.Media.Animation

open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.ExternalAccess.FSharp.Classification
open Microsoft.CodeAnalysis.ExternalAccess.FSharp.Editor.Shared.Extensions

open FSharp.Compiler
open FSharp.Compiler.SourceCodeServices
open FSharp.Compiler.Range

open Microsoft.VisualStudio.FSharp.Editor.Logging

open Microsoft.VisualStudio.Shell.Interop

open Microsoft.VisualStudio.Text
open Microsoft.VisualStudio.Text.Classification

open Internal.Utilities.StructuredFormat

open Microsoft.CodeAnalysis.ExternalAccess.FSharp.Editor.Shared.Utilities

type internal FSharpCodeLensService
    (
        serviceProvider: IServiceProvider,
        workspace: Workspace, 
        documentId: Lazy<DocumentId>,
        buffer: ITextBuffer, 
        checker: FSharpChecker,
        projectInfoManager: FSharpProjectOptionsManager,
        classificationFormatMapService: IClassificationFormatMapService,
        typeMap: Lazy<FSharpClassificationTypeMap>,
        codeLensDisplayService: CodeLensDisplayService,
        settings: EditorOptions
    ) as self =

    static let userOpName = "FSharpCodeLensService"

    let visit pos parseTree = 
        AstTraversal.Traverse(pos, parseTree, { new AstTraversal.AstVisitorBase<_>() with 
            member _.VisitExpr(_, _, defaultTraverse, expr) =
                defaultTraverse(expr)
            
            override _.VisitInheritSynMemberDefn (_, _, _, _, range) = Some range

            override _.VisitTypeAbbrev( _, range) = Some range

            override _.VisitLetOrUse(_, _, bindings, range) =
                match bindings |> Seq.tryFind (fun b -> b.RangeOfHeadPat.StartLine = pos.Line) with
                | Some entry ->
                    Some entry.RangeOfBindingAndRhs
                | None ->
                    // We choose to use the default range because
                    // it wasn't possible to find the complete range
                    // including implementation code.
                    Some range

            override _.VisitBinding (_, binding) =
                Some binding.RangeOfBindingAndRhs
        })

    let formatMap = lazy classificationFormatMapService.GetClassificationFormatMap "tooltip" // TODO - play with other values, ideally 'codelens'
    let mutable bufferChangedCts = new CancellationTokenSource()
    let uiContext = SynchronizationContext.Current

    let layoutTagToFormatting (layoutTag: LayoutTag) =
        layoutTag
        |> RoslynHelpers.roslynTag
        |> FSharpClassificationTags.GetClassificationTypeName
        |> typeMap.Value.GetClassificationType
        |> formatMap.Value.GetTextProperties   

    let createTextBox (lensInfo: Option<ResizeArray<Layout.TaggedText> * QuickInfoNavigation>) =
        lensInfo
        |> Option.map(fun (taggedText, navigation) ->
            let textBlock = new TextBlock(Background = Brushes.AliceBlue, Opacity = 0.0, TextTrimming = TextTrimming.None)
            FSharpDependencyObjectExtensions.SetDefaultTextProperties(textBlock, formatMap.Value)

            for text in taggedText do
                let coloredProperties = layoutTagToFormatting text.Tag
                let actualProperties =
                    if settings.Advanced.CodeLensOptions.UseColors then
                        // If color is gray (R=G=B), change to correct gray color.
                        // Otherwise, use the provided color.
                        match coloredProperties.ForegroundBrush with
                        | :? SolidColorBrush as b ->
                            let c = b.Color
                            if c.R = c.G && c.R = c.B
                            then coloredProperties.SetForeground(Color.FromRgb(153uy, 153uy, 153uy))
                            else coloredProperties
                        | _ -> coloredProperties
                    else
                        coloredProperties.SetForeground(Color.FromRgb(153uy, 153uy, 153uy))

                let run = Documents.Run text.Text
                FSharpDependencyObjectExtensions.SetTextProperties (run, actualProperties)

                let inl =
                    match text with
                    | :? Layout.NavigableTaggedText as nav when navigation.IsTargetValid nav.Range ->
                        let h = Documents.Hyperlink(run, ToolTip = nav.Range.FileName)
                        h.Click.Add (fun _ -> 
                            navigation.NavigateTo nav.Range)
                        h :> Documents.Inline
                    | _ -> run :> _
                FSharpDependencyObjectExtensions.SetTextProperties (inl, actualProperties)
                textBlock.Inlines.Add inl

            textBlock.Measure(Size(Double.PositiveInfinity, Double.PositiveInfinity))
            textBlock :> UIElement)

    let executeCodeLenseAsync () =  
        asyncMaybe {
            let! document = workspace.CurrentSolution.GetDocument(documentId.Value) |> Option.ofObj
            let! _, options = projectInfoManager.TryGetOptionsForEditingDocumentOrProject(document, bufferChangedCts.Token, userOpName)
            let! _, parsedInput, checkFileResults = checker.ParseAndCheckDocument(document, options, userOpName=userOpName)
            let! symbolUses = checkFileResults.GetAllUsesOfAllSymbolsInFile() |> liftAsync
            let textSnapshot = buffer.CurrentSnapshot

            let unattachedSymbols = ResizeArray()
            let lensInfoToAdd = ResizeArray()

            // TODO - take a look, does it need to still be written this way?
            let useResults (displayContext: FSharpDisplayContext) (func: FSharpMemberOrFunctionOrValue) (realPosition: range) =
                let lineNumber = Line.toZ func.DeclarationLocation.StartLine
                if (lineNumber >= 0 || lineNumber < textSnapshot.LineCount) then
                    let typeLayout = func.FormatLayout displayContext
                    let taggedText = ResizeArray()        
                    Layout.renderL (Layout.taggedTextListR taggedText.Add) typeLayout |> ignore
                    let statusBar = StatusBar(serviceProvider.GetService<SVsStatusbar, IVsStatusbar>()) 
                    let navigation = QuickInfoNavigation(statusBar, checker, projectInfoManager, document, realPosition)
                    Some(taggedText, navigation)
                else
                    None
                
            for symbolUse in symbolUses do
                if symbolUse.IsFromDefinition then
                    match symbolUse.Symbol with
                    | :? FSharpMemberOrFunctionOrValue as func when func.IsModuleValueOrMember || func.IsProperty ->
                        unattachedSymbols.Add((symbolUse.DisplayContext, func))
                    | _ -> ()

            for (displayContext, func) in unattachedSymbols do
                let declarationLine, range = 
                    match visit func.DeclarationLocation.Start parsedInput with
                    | Some range -> range.StartLine - 1, range
                    | _ -> func.DeclarationLocation.StartLine - 1, func.DeclarationLocation

                let lensInfo = useResults displayContext func range

                let declarationSpan = 
                    let line = textSnapshot.GetLineFromLineNumber declarationLine
                    let offset = line.GetText() |> Seq.findIndex (Char.IsWhiteSpace >> not)
                    SnapshotSpan(line.Start.Add offset, line.End).Span

                let trackingSpan = textSnapshot.CreateTrackingSpan(declarationSpan, SpanTrackingMode.EdgeExclusive)
                lensInfoToAdd.Add (trackingSpan, lensInfo)


            let createCodeLensUIElement codelensInfo trackingSpan _ =
                match createTextBox codelensInfo with
                | Some uiElement ->
                    let animation = 
                        DoubleAnimation(
                            To = Nullable 0.8,
                            Duration = Duration(TimeSpan.FromMilliseconds 1000.0),
                            EasingFunction = QuadraticEase())
                    let sb = Storyboard()
                    Storyboard.SetTarget(sb, uiElement)
                    Storyboard.SetTargetProperty(sb, PropertyPath Control.OpacityProperty)
                    sb.Children.Add animation
                    codeLensDisplayService.AddUiElementToCodeLensOnce (trackingSpan, uiElement)
                    codeLensDisplayService.RelayoutRequested.Enqueue ()
                    sb.Begin()
                | None ->
                    ()
                        
            // Unclear why this is needed - TODO investigate            
            do! Async.SwitchToContext uiContext |> liftAsync

            for (trackingSpan, codeLensInfo) in lensInfoToAdd do
                let grid = codeLensDisplayService.AddCodeLens trackingSpan
                grid.IsVisibleChanged
                |> Event.filter (fun eventArgs -> eventArgs.NewValue :?> bool)
                |> Event.add (createCodeLensUIElement codeLensInfo trackingSpan)
        }
        |> Async.Ignore
    
    do
        buffer.Changed.AddHandler(fun _ e -> (self.BufferChanged e))
        async {
            try
                do! executeCodeLenseAsync()
            with
            | e ->
#if DEBUG
                logExceptionWithContext (e, "CodeLens startup failed")
#else
                ignore e
#endif
        } |> Async.Start

    member _.BufferChanged _ =
        bufferChangedCts.Cancel() // Stop all ongoing async workflow. 
        bufferChangedCts.Dispose()
        bufferChangedCts <- new CancellationTokenSource()
        executeCodeLenseAsync ()
        |> RoslynHelpers.StartAsyncSafe bufferChangedCts.Token "Buffer Changed"
