﻿// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.
namespace Microsoft.VisualStudio.FSharp.Editor

open Microsoft.VisualStudio.Shell

open System
open System.Collections.Immutable
open System.Threading
open System.ComponentModel.Composition

open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.Text
open Microsoft.CodeAnalysis.ExternalAccess.FSharp.InlineHints

open FSharp.Compiler
open FSharp.Compiler.SourceCodeServices

[<Export(typeof<IFSharpInlineHintsService>)>]
type internal FSharpInlineHintsService
    [<ImportingConstructor>]
    (
        checkerProvider: FSharpCheckerProvider,
        [<Import(typeof<SVsServiceProvider>)>] serviceProvider: IServiceProvider,
        projectInfoManager: FSharpProjectOptionsManager
    ) =

    static let userOpName = "FSharpInlineHints"

    interface IFSharpInlineHintsService with
        member _.GetInlineHintsAsync(document: Document, textSpan: TextSpan, cancellationToken: CancellationToken) =
            asyncMaybe {
                do! Option.guard (not (isSignatureFile document.FilePath))

                let! textVersion = document.GetTextVersionAsync(cancellationToken)
                let! parsingOptions, projectOptions = projectInfoManager.TryGetOptionsForEditingDocumentOrProject(document, cancellationToken, userOpName)
                let! sourceText = document.GetTextAsync(cancellationToken)
                let! parseFileResults, _, checkFileResults = checkerProvider.Checker.ParseAndCheckDocument(document, projectOptions, userOpName)
                let range = RoslynHelpers.TextSpanToFSharpRange(document.FilePath, textSpan, sourceText)
                let! symbolUses = checkFileResults.GetAllUsesOfAllSymbolsInFileWithinRange(range) |> liftAsync

                let typeHints = ImmutableArray.CreateBuilder()
                let parameterHints = ImmutableArray.CreateBuilder()

                let isValid (funcOrValue: FSharpMemberOrFunctionOrValue) (symbolUse: FSharpSymbolUse) =
                    not (parseFileResults.IsTypeAnnotationGiven symbolUse.RangeAlternate.Start) &&
                    symbolUse.IsFromDefinition &&
                    (funcOrValue.IsValue || funcOrValue.IsFunction) &&
                    not funcOrValue.IsMember &&
                    not funcOrValue.IsMemberThisValue &&
                    not funcOrValue.IsConstructorThisValue &&
                    not (PrettyNaming.IsOperatorName funcOrValue.DisplayName)

                for symbolUse in symbolUses |> Array.distinctBy (fun su -> su.RangeAlternate) do
                    match symbolUse.Symbol with
                    | :? FSharpMemberOrFunctionOrValue as funcOrValue when isValid funcOrValue symbolUse ->
                        let typeInfo = ResizeArray()
                            
                        funcOrValue.FormatLayout symbolUse.DisplayContext
                        |> Layout.renderL (Layout.taggedTextListR typeInfo.Add)
                        |> ignore
                            
                        let displayParts = ImmutableArray.CreateBuilder()
                        displayParts.Add(TaggedText(TextTags.Text, ": "))

                        for tt in typeInfo do
                            displayParts.Add(TaggedText(RoslynHelpers.roslynTag tt.Tag, tt.Text))

                        // TODO - this is not actually correct
                        // We need to get QuickInfo for the actual type we pull out, not the value
                        // But it does demonstrate a possible way to do this
                        let callBack position =
                            fun _ _ ->
                                asyncMaybe {
                                    let! quickInfo =
                                        FSharpAsyncQuickInfoSource.ProvideQuickInfo(
                                            checkerProvider.Checker,
                                            document.Id,
                                            sourceText,
                                            document.FilePath,
                                            position,
                                            parsingOptions,
                                            projectOptions,
                                            textVersion.GetHashCode(),
                                            document.FSharpOptions.LanguageServicePerformance)

                                    let documentationBuilder = XmlDocumentation.CreateDocumentationBuilder(serviceProvider.XMLMemberIndexService)
                                    let mainDesc, docs  = FSharpAsyncQuickInfoSource.BuildSingleQuickInfoItem documentationBuilder quickInfo

                                    let descriptionParts = ImmutableArray.CreateBuilder()

                                    for tt in mainDesc do
                                        descriptionParts.Add(TaggedText(RoslynHelpers.roslynTag tt.Tag, tt.Text))

                                    for tt in docs do
                                        descriptionParts.Add(TaggedText(RoslynHelpers.roslynTag tt.Tag, tt.Text))

                                    return (descriptionParts.ToImmutableArray())
                                }
                                |> Async.map (Option.defaultValue ImmutableArray<_>.Empty)
                                |> RoslynHelpers.StartAsyncAsTask(cancellationToken)

                        let getDescriptionAsync position = Func<Document, CancellationToken, _>(callBack position)
                        let symbolSpan = RoslynHelpers.FSharpRangeToTextSpan(sourceText, symbolUse.RangeAlternate)

                        let hint = FSharpInlineHint(TextSpan(symbolSpan.End, 0), displayParts.ToImmutableArray(), getDescriptionAsync symbolSpan.Start)
                        typeHints.Add(hint)

                    | :? FSharpMemberOrFunctionOrValue as func when func.IsFunction && not symbolUse.IsFromDefinition ->
                        let appliedArgRangesOpt = parseFileResults.GetAllArgumentsForFunctionApplication symbolUse.RangeAlternate.Start
                        match appliedArgRangesOpt with
                        | Some [] -> ()
                        | Some appliedArgRanges ->
                            match func.PossibleArgumentList with
                            | Some [] -> ()
                            | Some definitionArgNames ->

                                let appliedArgRanges = appliedArgRanges |> Array.ofList
                                let definitionArgNames = definitionArgNames |> Array.ofList

                                for idx = 0 to appliedArgRanges.Length - 1 do
                                    let appliedArgRange = appliedArgRanges.[idx]
                                    let definitionArgName = definitionArgNames.[idx]
                                    let appledArgSpan = RoslynHelpers.FSharpRangeToTextSpan(sourceText, appliedArgRange)
                                    let displayParts = ImmutableArray.Create(TaggedText(TextTags.Text, definitionArgName + ": "))
                                    let hint = FSharpInlineHint(TextSpan(appledArgSpan.Start, 0), displayParts)
                                    parameterHints.Add(hint)
                            | _ ->
                                ()
                        | None ->
                            ()

                        ()

                    // TODO - support method calls, ctors, etc

                    | _ -> ()

                let typeHints = typeHints.ToImmutableArray()
                let parameterHints = parameterHints.ToImmutableArray()

                return typeHints.AddRange(parameterHints)
            }
            |> Async.map (Option.defaultValue ImmutableArray<_>.Empty)
            |> RoslynHelpers.StartAsyncAsTask(cancellationToken)
