"control" use

"String.String" use

"astNodeType.MultiParserResult" use
"builtins.initBuiltins" use
"codeNode.addBlock" use
"codeNode.addBlock" use
"NameManager.NameManager" use
"processor.NameInfoEntry" use
"processor.ProcessorOptions" use

{
  program: String Ref;
  result: String Ref;
  unitId: 0;
  options: ProcessorOptions Cref;
  nameManager: NameInfoEntry NameManager Ref;
  multiParserResult: MultiParserResult Cref;
} () {convention: cdecl;} [
  program:;
  result:;
  copy unitId:;
  options:;
  nameManager:;
  multiParserResult:;

  processor: Processor;

  unitId @processor.@unitId set
  @nameManager move @processor.@nameManager set
  @options @processor.@options set
  multiParserResult @processor.!multiParserResult

  ""           findNameInfo @processor.@emptyNameInfo set
  "CALL"       findNameInfo @processor.@callNameInfo set
  "PRE"        findNameInfo @processor.@preNameInfo set
  "DIE"        findNameInfo @processor.@dieNameInfo set
  "INIT"       findNameInfo @processor.@initNameInfo set
  "ASSIGN"     findNameInfo @processor.@assignNameInfo set
  "self"       findNameInfo @processor.@selfNameInfo set
  "closure"    findNameInfo @processor.@closureNameInfo set
  "inputs"     findNameInfo @processor.@inputsNameInfo set
  "outputs"    findNameInfo @processor.@outputsNameInfo set
  "captures"   findNameInfo @processor.@capturesNameInfo set
  "variadic"   findNameInfo @processor.@variadicNameInfo set
  "failProc"   findNameInfo @processor.@failProcNameInfo set
  "convention" findNameInfo @processor.@conventionNameInfo set

  addBlock
  TRUE dynamic @processor.@blocks.last.get.@root set

  @processor initBuiltins

  s1: String;
  s2: String;
  processor.options.pointerSize 32nx = [
    "target datalayout = \"e-m:x-p:32:32-i64:64-f80:32-n8:16:32-a:0:32-S32\"" makeStringView addStrToProlog
    "target triple = \"i386-pc-windows-msvc18.0.0\"" makeStringView addStrToProlog
  ] [
    "target datalayout = \"e-m:w-i64:64-f80:128-n8:16:32:64-S128\"" makeStringView addStrToProlog
    "target triple = \"x86_64-pc-windows\"" makeStringView addStrToProlog
  ] if

  "" makeStringView addStrToProlog
  ("mainPath is \"" makeStringView processor.options.mainPath makeStringView "\"" makeStringView) addLog

  processor.options.callTrace [createCallTraceData] when

  addLinkerOptionsDebugInfo

  processor.options.fileNames.size @processor.@files.resize
  processor.options.fileNames.size [
    File owner i @processor.@files.at set
    i processor.options.fileNames.at copy i @processor.@files.at.get.!name
  ] times

  processor.options.debug [
    @processor [processor:; addDebugProlog @processor.@debugInfo.@unit set] call

    processor.files.size [
      i processor.files.at.get.name addFileDebugInfo i @processor.@files.at.get.!debugId
    ] times
  ] when

  lastFile: File Cref;

  multiParserResult.nodes.dataSize 0 > [

    dependedFiles: String IndexArray HashTable; # string -> array of indexes of dependent files
    cachedGlobalErrorInfoSize: 0;

    runFile: [
      n:;
      file: n @processor.@files.at.get;
      file !lastFile
      fileNode: n processor.multiParserResult.nodes.at;
      rootPositionInfo: CompilerPositionInfo;
      file @rootPositionInfo.@file.set
      1    @rootPositionInfo.!line
      1    @rootPositionInfo.!column

      processor.result.globalErrorInfo.getSize @cachedGlobalErrorInfoSize set
      topNodeIndex: StringView 0 NodeCaseCode @processor fileNode file rootPositionInfo CFunctionSignature astNodeToCodeNode;

      processor.result.findModuleFail [
        # cant compile this file now, add him to queue
        ("postpone compilation of \"" file.name "\" because \"" processor.result.errorInfo.missedModule "\" is not compiled yet") addLog
        fr: processor.result.errorInfo.missedModule makeStringView @dependedFiles.find;
        fr.success [
          n @fr.@value.pushBack
        ] [
          a: IndexArray;
          n @a.pushBack
          @processor.result.@errorInfo.@missedModule @a move @dependedFiles.insert
        ] if

        cachedGlobalErrorInfoSize @processor.@result clearProcessorResult
      ] [
        moduleName: file.name;
        ("compiled file " moduleName) addLog

        topNodeIndex @processor.@blocks.at.get @file.@rootBlock.set

        moduleName stripExtension extractFilename toString !moduleName
        moduleName topNodeIndex @processor.@modules.insert
        moduleName copy topNodeIndex @processor.@blocks.at.get.!moduleName

        # call files which depends from this module
        moduleName.size 0 > [
          fr: moduleName @dependedFiles.find;
          fr.success [
            i: 0 dynamic;
            [
              i fr.value.dataSize < [
                numberOfDependent: fr.value.dataSize 1 - i - fr.value.at;
                (numberOfDependent processor.files.at.get.name " is dependent from it, try to recompile") addLog
                numberOfDependent @unfinishedFiles.pushBack
                i 1 + @i set TRUE
              ] &&
            ] loop

            @fr.@value.clear
          ] when

        ] when
      ] if
    ];

    unfinishedFiles: IndexArray;
    n: 0 dynamic;
    [
      n processor.multiParserResult.nodes.dataSize < [
        processor.multiParserResult.nodes.dataSize 1 - n - @unfinishedFiles.pushBack
        n 1 + @n set TRUE
      ] &&
    ] loop

    [
      0 unfinishedFiles.dataSize < [
        n: unfinishedFiles.last copy;
        @unfinishedFiles.popBack
        n runFile
        processor.result.success copy
      ] &&
    ] loop

    processor.result.success ~ [
      @processor.@result.@errorInfo move @processor.@result.@globalErrorInfo.pushBack
    ] when

    processor.result.globalErrorInfo.getSize 0 > [
      FALSE @processor.@result.@success set
    ] when

    processor.result.success [
      processor.options.debug [
        lastFile correctUnitInfo
      ] when

      0 @processor.@result clearProcessorResult

      dependedFiles.getSize 0 > [
        hasError: FALSE dynamic;
        hasErrorMessage: FALSE dynamic;
        dependedFiles [
          # queue is empty, but has uncompiled files
          pair:;
          pair.value.dataSize 0 > [
            fr: pair.key processor.modules.find;
            fr.success ~ [
              ("missing module \"" @pair.@key "\" used in file: \"" pair.value.last processor.options.fileNames.at "\"" LF) assembleString @processor.@result.@errorInfo.@message.cat
              TRUE @hasErrorMessage set
            ] when
            TRUE @hasError set
            FALSE @processor.@result.@success set
          ] when
        ] each

        hasError [hasErrorMessage ~] && [
          String @processor.@result.@errorInfo.@message set
          "problem with finding modules" @processor.@result.@errorInfo.@message.cat

          LF @processor.@result.@errorInfo.@message.cat
          dependedFiles [
            # queue is empty, but has uncompiled files
            pair:;
            pair.value.dataSize 0 > [
              ("need module: " @pair.@key "; used in file: " pair.value.last processor.options.fileNames.at LF) assembleString @processor.@result.@errorInfo.@message.cat
            ] when
          ] each
        ] when

        processor.result.success ~ [
          @processor.@result.@errorInfo move @processor.@result.@globalErrorInfo.pushBack
        ] when
      ] when
    ] when
  ] when


  ("all nodes generated" makeStringView) addLog
  [processor compilable ~ [processor.recursiveNodesStack.getSize 0 =] ||] "Recursive stack is not empty!" assert

  processor.result.success [
    ("nameCount=" processor.nameManager.names.dataSize
      "; irNameCount=" processor.nameBuffer.dataSize) addLog

    ("max depth of recursion=" processor.maxDepthOfRecursion) addLog

    processor.usedFloatBuiltins [createFloatBuiltins] when
    processor.options.callTrace processor.options.threadModel 1 = and createCtors
    createDtors
    clearUnusedDebugInfo
    addAliasesForUsedNodes

    i: 0 dynamic;
    [
      i processor.prolog.dataSize < [
        i @processor.@prolog.at @processor.@result.@program.cat
        LF  @processor.@result.@program.cat
        i 1 + @i set TRUE
      ] &&
    ] loop

    i: 1 dynamic; # 0th node is root fake node
    [
      i processor.blocks.dataSize < [
        block: i @processor.@blocks.at.get;
        block nodeHasCode [
          LF makeStringView @processor.@result.@program.cat

          block.header makeStringView @processor.@result.@program.cat

          block.nodeCase NodeCaseDeclaration = ~ [
            " {" @processor.@result.@program.cat
            LF   @processor.@result.@program.cat

            block.program [
              curInstruction:;
              curInstruction.enabled [
                block.programTemplate.getStringView curInstruction.codeOffset curInstruction.codeSize view @processor.@result.@program.cat
                LF @processor.@result.@program.cat
              ] [
              ] if
            ] each
            "}" @processor.@result.@program.cat
          ] when
          LF @processor.@result.@program.cat
        ] when
        i 1 + @i set TRUE
      ] &&
    ] loop

    LF @processor.@result.@program.cat

    processor.debugInfo.strings [
      s:;
      s.size 0 = ~ [
        s @processor.@result.@program.cat
        LF @processor.@result.@program.cat
      ] when
    ] each
  ] when

  processor.result.success ~ [
    processor.result.globalErrorInfo.getSize [
      current: i processor.result.globalErrorInfo @;
      i 0 > [LF @result.cat] when
      current.position.getSize 0 = [
        ("error, "  current.message LF) [@result.cat] each
      ] [
        current.position.getSize [
          nodePosition: i current.position @;
          (nodePosition.file.name "(" nodePosition.line  ","  nodePosition.column "): ") [@result.cat] each

          i 0 = [
            ("error, [" nodePosition.token "], " current.message LF) [@result.cat] each
          ] [
            ("[" nodePosition.token "], called from here" LF) [@result.cat] each
          ] if
        ] times
      ] if
    ] times
  ] [
    @processor.@result.@program move @program set
  ] if
] "process" exportFunction

{
  signature: CFunctionSignature Cref;
  compilerPositionInfo: CompilerPositionInfo Cref;
  processor: Processor Ref;
  refToVar: RefToVar Cref;
} () {convention: cdecl;} [
  forcedSignature:;
  compilerPositionInfo:;
  processor:;
  refToVar:;

  addBlock
  codeNode: @processor.@blocks.last.get;
  block: @codeNode;
  failProc: @failProcForProcessor;

  NodeCaseDtor @codeNode.@nodeCase set
  0 dynamic @codeNode.@parent set
  @compilerPositionInfo @codeNode.@position set

  processor.options.debug [
    @processor addDebugReserve @codeNode.@funcDbgIndex set
  ] when

  begin: RefToVar;
  end: RefToVar;
  refToVar @begin @end ShadowReasonCapture @block makeShadows

  VarStruct refToVar getVar.data .get.get .unableToDie
  VarStruct @end     getVar.@data.get.get.@unableToDie set # fake becouse it is fake shadow

  end killStruct
  dtorName: ("dtor." refToVar getVar.globalId) assembleString;
  dtorNameStringView: dtorName makeStringView;
  dtorNameStringView finalizeCodeNode
] "createDtorForGlobalVar" exportFunction
