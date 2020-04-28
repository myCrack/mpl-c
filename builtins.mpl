"control" use
"builtinImpl" use

"String.print" use
"String.toString" use
"conventions.cdecl" use

"Block.Block" use
"Block.NameCaseBuiltin" use
"astNodeType.MultiParserResult" use
"defaultImpl.failProcForProcessor" use
"processor.Processor" use
"processor.ProcessorResult" use
"variable.NameInfo" use
"variable.getMplType" use
"variable.getVar" use

builtins: (
  {name: "!"                       ; impl: @mplBuiltinExclamation             ;}
  {name: "&"                       ; impl: @mplBuiltinStrCat                  ;}
  {name: "*"                       ; impl: @mplBuiltinMul                     ;}
  {name: "+"                       ; impl: @mplBuiltinAdd                     ;}
  {name: "-"                       ; impl: @mplBuiltinSub                     ;}
  {name: "/"                       ; impl: @mplBuiltinDiv                     ;}
  {name: "<"                       ; impl: @mplBuiltinLess                    ;}
  {name: "="                       ; impl: @mplBuiltinEqual                   ;}
  {name: ">"                       ; impl: @mplBuiltinGreater                 ;}
  {name: "@"                       ; impl: @mplBuiltinAt                      ;}
  {name: "COMPILER_VERSION"        ; impl: @mplBuiltinCompilerVersion         ;}
  {name: "DEBUG"                   ; impl: @mplBuiltinDebug                   ;}
  {name: "FALSE"                   ; impl: @mplBuiltinFalse                   ;}
  {name: "HAS_LOGS"                ; impl: @mplBuiltinHasLogs                 ;}
  {name: "LF"                      ; impl: @mplBuiltinLF                      ;}
  {name: "TRUE"                    ; impl: @mplBuiltinTrue                    ;}
  {name: "^"                       ; impl: @mplBuiltinPow                     ;}
  {name: "addressToReference"      ; impl: @mplBuiltinAddressToReference      ;}
  {name: "alignment"               ; impl: @mplBuiltinAlignment               ;}
  {name: "and"                     ; impl: @mplBuiltinAnd                     ;}
  {name: "array"                   ; impl: @mplBuiltinArray                   ;}
  {name: "call"                    ; impl: @mplBuiltinCall                    ;}
  {name: "callField"               ; impl: @mplBuiltinCallField               ;}
  {name: "cast"                    ; impl: @mplBuiltinCast                    ;}
  {name: "ceil"                    ; impl: @mplBuiltinCeil                    ;}
  {name: "codeRef"                 ; impl: @mplBuiltinCodeRef                 ;}
  {name: "compileOnce"             ; impl: @mplBuiltinCompileOnce             ;}
  {name: "const"                   ; impl: @mplBuiltinConst                   ;}
  {name: "copy"                    ; impl: @mplBuiltinCopy                    ;}
  {name: "cos"                     ; impl: @mplBuiltinCos                     ;}
  {name: "def"                     ; impl: @mplBuiltinDef                     ;}
  {name: "dynamic"                 ; impl: @mplBuiltinDirty                   ;}
  {name: "exportFunction"          ; impl: @mplBuiltinExportFunction          ;}
  {name: "exportVariable"          ; impl: @mplBuiltinExportVariable          ;}
  {name: "failProc"                ; impl: @mplBuiltinFailProc                ;}
  {name: "fieldCount"              ; impl: @mplBuiltinFieldCount              ;}
  {name: "fieldIndex"              ; impl: @mplBuiltinFieldIndex              ;}
  {name: "fieldName"               ; impl: @mplBuiltinFieldName               ;}
  {name: "floor"                   ; impl: @mplBuiltinFloor                   ;}
  {name: "getCallTrace"            ; impl: @mplBuiltinGetCallTrace            ;}
  {name: "has"                     ; impl: @mplBuiltinHas                     ;}
  {name: "if"                      ; impl: @mplBuiltinIf                      ;}
  {name: "importFunction"          ; impl: @mplBuiltinImportFunction          ;}
  {name: "importVariable"          ; impl: @mplBuiltinImportVariable          ;}
  {name: "is"                      ; impl: @mplBuiltinIs                      ;}
  {name: "isCombined"              ; impl: @mplBuiltinIsCombined              ;}
  {name: "isConst"                 ; impl: @mplBuiltinIsConst                 ;}
  {name: "isMoved"                 ; impl: @mplBuiltinIsMoved                 ;}
  {name: "log"                     ; impl: @mplBuiltinLog                     ;}
  {name: "log10"                   ; impl: @mplBuiltinLog10                   ;}
  {name: "loop"                    ; impl: @mplBuiltinLoop                    ;}
  {name: "lshift"                  ; impl: @mplBuiltinLShift                  ;}
  {name: "manuallyDestroyVariable" ; impl: @mplBuiltinManuallyDestroyVariable ;}
  {name: "manuallyInitVariable"    ; impl: @mplBuiltinManuallyInitVariable    ;}
  {name: "mod"                     ; impl: @mplBuiltinMod                     ;}
  {name: "move"                    ; impl: @mplBuiltinMove                    ;}
  {name: "moveIf"                  ; impl: @mplBuiltinMoveIf                  ;}
  {name: "neg"                     ; impl: @mplBuiltinNeg                     ;}
  {name: "newVarOfTheSameType"     ; impl: @mplBuiltinNewVarOfTheSameType     ;}
  {name: "or"                      ; impl: @mplBuiltinOr                      ;}
  {name: "overload"                ; impl: @mplBuiltinOverload                ;}
  {name: "printCompilerMessage"    ; impl: @mplBuiltinPrintCompilerMessage    ;}
  {name: "printStack"              ; impl: @mplBuiltinPrintStack              ;}
  {name: "printStackTrace"         ; impl: @mplBuiltinPrintStackTrace         ;}
  {name: "printVariableCount"      ; impl: @mplBuiltinPrintVariableCount      ;}
  {name: "raiseStaticError"        ; impl: @mplBuiltinRaiseStaticError        ;}
  {name: "recursive"               ; impl: @mplBuiltinRecursive               ;}
  {name: "rshift"                  ; impl: @mplBuiltinRShift                  ;}
  {name: "same"                    ; impl: @mplBuiltinSame                    ;}
  {name: "schema"                  ; impl: @mplBuiltinSchema                  ;}
  {name: "set"                     ; impl: @mplBuiltinSet                     ;}
  {name: "sin"                     ; impl: @mplBuiltinSin                     ;}
  {name: "sqrt"                    ; impl: @mplBuiltinSqrt                    ;}
  {name: "static"                  ; impl: @mplBuiltinStatic                  ;}
  {name: "storageAddress"          ; impl: @mplBuiltinStorageAddress          ;}
  {name: "storageSize"             ; impl: @mplBuiltinStorageSize             ;}
  {name: "textSize"                ; impl: @mplBuiltinTextSize                ;}
  {name: "textSplit"               ; impl: @mplBuiltinTextSplit               ;}
  {name: "ucall"                   ; impl: @mplBuiltinUcall                   ;}
  {name: "uif"                     ; impl: @mplBuiltinUif                     ;}
  {name: "use"                     ; impl: @mplBuiltinUse                     ;}
  {name: "virtual"                 ; impl: @mplBuiltinVirtual                 ;}
  {name: "xor"                     ; impl: @mplBuiltinXor                     ;}
  {name: "~"                       ; impl: @mplBuiltinNot                     ;}
);

builtinFirst: [0 static];
builtinLast: [builtins fieldCount 0 cast 2 /];

addBuiltin: [
  copy id:;
  name:;

  nameId: @name makeStringView @processor.@nameManager.createName;
  bvar: @id VarBuiltin @block createVariable Virtual @block makeStaticity;

  {
    addNameCase: NameCaseBuiltin;
    refToVar:    bvar copy;
    nameInfo:    nameId copy;
  } addNameInfo
];

initBuiltins: [
  processor:;
  codeNode: 0 @processor.@blocks.at.get;
  block: @codeNode;
  failProc: @failProcForProcessor;

  builtins fieldCount dynamic [
    i builtins @ .name makeStringView i addBuiltin
  ] times
];

{processor: Processor Ref; block: Block Ref; multiParserResult: MultiParserResult Cref; index: Int32;} () {convention: cdecl;} [
  processor:;
  block:;
  multiParserResult:;
  failProc: @failProcForProcessor;
  copy index:;

  builtinFunc: index builtins @ .@impl;
  multiParserResult @block @processor @builtinFunc call
] "callBuiltinImpl" exportFunction
