
//  Microsoft (R) .NET Framework IL Disassembler.  Version 4.6.1055.0
//  Copyright (c) Microsoft Corporation.  All rights reserved.



// Metadata version: v4.0.30319
.assembly extern mscorlib
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )                         // .z\V.4..
  .ver 4:0:0:0
}
.assembly extern FSharp.Core
{
  .publickeytoken = (B0 3F 5F 7F 11 D5 0A 3A )                         // .?_....:
  .ver 4:5:0:0
}
.assembly TestFunction3c
{
  .custom instance void [FSharp.Core]Microsoft.FSharp.Core.FSharpInterfaceDataVersionAttribute::.ctor(int32,
                                                                                                      int32,
                                                                                                      int32) = ( 01 00 02 00 00 00 00 00 00 00 00 00 00 00 00 00 ) 

  // --- The following custom attribute is added automatically, do not uncomment -------
  //  .custom instance void [mscorlib]System.Diagnostics.DebuggableAttribute::.ctor(valuetype [mscorlib]System.Diagnostics.DebuggableAttribute/DebuggingModes) = ( 01 00 01 01 00 00 00 00 ) 

  .hash algorithm 0x00008004
  .ver 0:0:0:0
}
.mresource public FSharpSignatureData.TestFunction3c
{
  // Offset: 0x00000000 Length: 0x00000208
}
.mresource public FSharpSignatureDataB.TestFunction3c
{
  // Offset: 0x00000210 Length: 0x00000006
}
.mresource public FSharpOptimizationData.TestFunction3c
{
  // Offset: 0x00000220 Length: 0x0000008A
}
.mresource public FSharpOptimizationDataB.TestFunction3c
{
  // Offset: 0x000002B0 Length: 0x00000000
}
.module TestFunction3c.exe
// MVID: {5C6C932B-16B2-1D41-A745-03832B936C5C}
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003       // WINDOWS_CUI
.corflags 0x00000001    //  ILONLY
// Image base: 0x00300000


// =============== CLASS MEMBERS DECLARATION ===================

.class public abstract auto ansi sealed TestFunction3c
       extends [mscorlib]System.Object
{
  .custom instance void [FSharp.Core]Microsoft.FSharp.Core.CompilationMappingAttribute::.ctor(valuetype [FSharp.Core]Microsoft.FSharp.Core.SourceConstructFlags) = ( 01 00 07 00 00 00 00 00 ) 
  .method public static int32  TestFunction1() cil managed
  {
    // Code size       36 (0x24)
    .maxstack  8
    .language '{AB4F38C9-B6E6-43BA-BE3B-58080B2CCCE3}', '{994B45C4-E6E9-11D2-903F-00C04FA302A1}', '{5A869D0B-6611-11D3-BD2A-0000F80849BD}'
    .line 5,5 : 5,20 'C:\\GitHub\\dsyme\\visualfsharp\\tests\\fsharpqa\\Source\\CodeGen\\EmittedIL\\TestFunctions\\TestFunction3c.fs'
    IL_0000:  ldstr      "Hello"
    IL_0005:  newobj     instance void class [FSharp.Core]Microsoft.FSharp.Core.PrintfFormat`5<class [FSharp.Core]Microsoft.FSharp.Core.Unit,class [mscorlib]System.IO.TextWriter,class [FSharp.Core]Microsoft.FSharp.Core.Unit,class [FSharp.Core]Microsoft.FSharp.Core.Unit,class [FSharp.Core]Microsoft.FSharp.Core.Unit>::.ctor(string)
    IL_000a:  call       !!0 [FSharp.Core]Microsoft.FSharp.Core.ExtraTopLevelOperators::PrintFormatLine<class [FSharp.Core]Microsoft.FSharp.Core.Unit>(class [FSharp.Core]Microsoft.FSharp.Core.PrintfFormat`4<!!0,class [mscorlib]System.IO.TextWriter,class [FSharp.Core]Microsoft.FSharp.Core.Unit,class [FSharp.Core]Microsoft.FSharp.Core.Unit>)
    IL_000f:  pop
    .line 6,6 : 5,20 ''
    IL_0010:  ldstr      "World"
    IL_0015:  newobj     instance void class [FSharp.Core]Microsoft.FSharp.Core.PrintfFormat`5<class [FSharp.Core]Microsoft.FSharp.Core.Unit,class [mscorlib]System.IO.TextWriter,class [FSharp.Core]Microsoft.FSharp.Core.Unit,class [FSharp.Core]Microsoft.FSharp.Core.Unit,class [FSharp.Core]Microsoft.FSharp.Core.Unit>::.ctor(string)
    IL_001a:  call       !!0 [FSharp.Core]Microsoft.FSharp.Core.ExtraTopLevelOperators::PrintFormatLine<class [FSharp.Core]Microsoft.FSharp.Core.Unit>(class [FSharp.Core]Microsoft.FSharp.Core.PrintfFormat`4<!!0,class [mscorlib]System.IO.TextWriter,class [FSharp.Core]Microsoft.FSharp.Core.Unit,class [FSharp.Core]Microsoft.FSharp.Core.Unit>)
    IL_001f:  pop
    .line 7,7 : 5,8 ''
    IL_0020:  ldc.i4.3
    IL_0021:  ldc.i4.4
    IL_0022:  add
    IL_0023:  ret
  } // end of method TestFunction3c::TestFunction1

  .method public static void  TestFunction3c() cil managed
  {
    // Code size       105 (0x69)
    .maxstack  4
    .locals init ([0] class [FSharp.Core]Microsoft.FSharp.Core.Unit V_0,
             [1] int32 x,
             [2] string V_2,
             [3] class [mscorlib]System.Exception V_3,
             [4] class [FSharp.Core]Microsoft.FSharp.Core.FSharpOption`1<string> V_4,
             [5] string msg,
             [6] string V_6)
    .line 11,11 : 8,31 ''
    .try
    {
      IL_0000:  call       int32 TestFunction3c::TestFunction1()
      IL_0005:  stloc.1
      .line 12,12 : 8,24 ''
      IL_0006:  ldstr      "hello"
      IL_000b:  stloc.2
      IL_000c:  ldloc.2
      IL_000d:  call       class [mscorlib]System.Exception [FSharp.Core]Microsoft.FSharp.Core.Operators::Failure(string)
      IL_0012:  throw

      .line 13,13 : 5,9 ''
    }  // end .try
    catch [mscorlib]System.Object 
    {
      IL_0013:  castclass  [mscorlib]System.Exception
      IL_0018:  stloc.3
      IL_0019:  ldloc.3
      IL_001a:  call       class [FSharp.Core]Microsoft.FSharp.Core.FSharpOption`1<string> [FSharp.Core]Microsoft.FSharp.Core.Operators::FailurePattern(class [mscorlib]System.Exception)
      IL_001f:  stloc.s    V_4
      IL_0021:  ldloc.s    V_4
      IL_0023:  brfalse.s  IL_005b

      IL_0025:  ldloc.s    V_4
      IL_0027:  call       instance !0 class [FSharp.Core]Microsoft.FSharp.Core.FSharpOption`1<string>::get_Value()
      IL_002c:  stloc.s    msg
      IL_002e:  ldloc.s    msg
      IL_0030:  ldstr      "hello"
      IL_0035:  call       bool [mscorlib]System.String::Equals(string,
                                                                string)
      IL_003a:  brfalse.s  IL_003e

      IL_003c:  br.s       IL_0040

      IL_003e:  br.s       IL_005b

      IL_0040:  ldloc.s    V_4
      IL_0042:  call       instance !0 class [FSharp.Core]Microsoft.FSharp.Core.FSharpOption`1<string>::get_Value()
      IL_0047:  stloc.s    V_6
      .line 14,14 : 8,23 ''
      IL_0049:  ldstr      "World"
      IL_004e:  newobj     instance void class [FSharp.Core]Microsoft.FSharp.Core.PrintfFormat`5<class [FSharp.Core]Microsoft.FSharp.Core.Unit,class [mscorlib]System.IO.TextWriter,class [FSharp.Core]Microsoft.FSharp.Core.Unit,class [FSharp.Core]Microsoft.FSharp.Core.Unit,class [FSharp.Core]Microsoft.FSharp.Core.Unit>::.ctor(string)
      IL_0053:  call       !!0 [FSharp.Core]Microsoft.FSharp.Core.ExtraTopLevelOperators::PrintFormatLine<class [FSharp.Core]Microsoft.FSharp.Core.Unit>(class [FSharp.Core]Microsoft.FSharp.Core.PrintfFormat`4<!!0,class [mscorlib]System.IO.TextWriter,class [FSharp.Core]Microsoft.FSharp.Core.Unit,class [FSharp.Core]Microsoft.FSharp.Core.Unit>)
      IL_0058:  stloc.0
      IL_0059:  leave.s    IL_0066

      .line 100001,100001 : 0,0 ''
      IL_005b:  rethrow
      IL_005d:  ldnull
      IL_005e:  unbox.any  [FSharp.Core]Microsoft.FSharp.Core.Unit
      IL_0063:  stloc.0
      IL_0064:  leave.s    IL_0066

      .line 100001,100001 : 0,0 ''
    }  // end handler
    IL_0066:  ldloc.0
    IL_0067:  pop
    IL_0068:  ret
  } // end of method TestFunction3c::TestFunction3c

} // end of class TestFunction3c

.class private abstract auto ansi sealed '<StartupCode$TestFunction3c>'.$TestFunction3c
       extends [mscorlib]System.Object
{
  .method public static void  main@() cil managed
  {
    .entrypoint
    // Code size       1 (0x1)
    .maxstack  8
    IL_0000:  ret
  } // end of method $TestFunction3c::main@

} // end of class '<StartupCode$TestFunction3c>'.$TestFunction3c


// =============================================================

// *********** DISASSEMBLY COMPLETE ***********************
