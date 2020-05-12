"control" use

"Array.Array" use
"HashTable.hash" use
"String.String" use
"String.StringView" use
"String.addLog" use
"String.asView" use
"String.assembleString" use
"String.hash" use
"String.makeStringView" use
"String.print" use
"String.toString" use

"Block.ArgCopy" use
"Block.ArgMeta" use
"Block.ArgGlobal" use
"Block.ArgRef" use
"Block.ArgRefDeref" use
"Block.ArgReturn" use
"Block.ArgReturnDeref" use
"Block.ArgVirtual" use
"Block.Block" use
"Block.BlockSchema" use
"Block.Capture" use
"Block.CFunctionSignature" use
"Block.CompilerPositionInfo" use
"Block.NameCaseInvalid" use
"Block.NameCaseLocal" use
"Block.NodeCaseCode" use
"Block.NodeCaseCodeRefDeclaration" use
"Block.NodeCaseDeclaration" use
"Block.NodeCaseExport" use
"Block.NodeCaseLambda" use
"Block.NodeCaseList" use
"Block.NodeCaseObject" use
"Block.NodeStateCompiled" use
"Block.NodeStateFailed" use
"Block.NodeStateHasOutput" use
"Block.NodeStateNew" use
"Block.NodeStateNoOutput" use
"Block.NodeRecursionStateFail" use
"Block.NodeRecursionStateNew" use
"Block.NodeRecursionStateNo" use
"Block.NodeRecursionStateOld" use
"Block.ShadowEvent" use
"File.File" use
"astNodeType.AstNode" use
"astNodeType.AstNodeType" use
"astNodeType.IndexArray" use
"codeNode.addBlock" use
"codeNode.addUnfoundedName" use
"codeNode.astNodeToCodeNode" use
"codeNode.captureName" use
"codeNode.deleteNode" use
"codeNode.finalizeCodeNode" use
"codeNode.getField" use
"codeNode.getFieldForMatching" use
"codeNode.getNameForMatching" use
"codeNode.getNameWithOverloadIndex" use
"codeNode.getNameForMatchingWithOverloadIndex" use
"codeNode.getPointeeNoDerefIR" use
"codeNode.getPointeeForMatching" use
"codeNode.getPossiblePointee" use
"codeNode.makeCompilerPosition" use
"codeNode.makePointeeDirtyIfRef" use
"codeNode.makeStaticity" use
"codeNode.makeVarDynamic" use
"codeNode.makeVarDirty" use
"codeNode.makeVarTreeDirty" use
"codeNode.makeVarTreeDynamic" use
"codeNode.makeVarTreeDirty" use
"codeNode.popForMatching" use
"codeNode.processStaticAt" use
"debugWriter.addDebugReserve" use
"declarations.compilerError" use
"declarations.copyOneVar" use
"declarations.copyVar" use
"declarations.copyVarFromChild" use
"declarations.copyVarToNew" use
"declarations.copyVarFromParent" use
"declarations.getMplType" use
"declarations.tryImplicitLambdaCast" use
"declarations.push" use
"defaultImpl.addShadowEvent" use
"defaultImpl.addEmptyCapture" use
"defaultImpl.compilable" use
"defaultImpl.FailProcForProcessor" use
"defaultImpl.findNameInfo" use
"defaultImpl.getStackDepth" use
"defaultImpl.getStackEntry" use
"defaultImpl.makeVarRealCaptured" use
"defaultImpl.pop" use
"defaultImpl.addStackUnderflowInfo" use
"irWriter.createAllocIR" use
"irWriter.createBranch" use
"irWriter.createCallIR" use
"irWriter.createComment" use
"irWriter.createCheckedCopyToNewNoDie" use
"irWriter.createDerefToRegister" use
"irWriter.createJump" use
"irWriter.createLabel" use
"irWriter.createPhiNode" use
"irWriter.createStaticInitIR" use
"irWriter.createStoreFromRegister" use
"irWriter.getMplSchema" use
"irWriter.getIrName" use
"irWriter.getIrType" use
"processor.IRArgument" use
"processor.Processor" use
"processor.ProcessorErrorInfo" use
"processor.ProcessorResult" use
"processor.RefToVarTable" use
"staticCall.staticCall" use
"Var.Dirty" use
"Var.Dynamic" use
"Var.isSemiplainNonrecursiveType" use
"Var.isNonrecursiveType" use
"Var.isSchema" use
"Var.isVirtual" use
"Var.fullUntemporize" use
"Var.getVar" use
"Var.staticityOfVar" use
"Var.RefToVar" use
"Var.ShadowReasonCapture" use
"Var.Static" use
"Var.VarBuiltin" use
"Var.VarCond" use
"Var.VarImport" use
"Var.VarRef" use
"Var.VarString" use
"Var.VarStruct" use
"Var.Virtual" use
"Var.Weak" use
"Var.variablesAreSame" use
"variable.isStaticData" use
"variable.isGlobal" use
"variable.markAsAbleToDie" use
"variable.noMatterToCopy" use
"variable.refsAreEqual" use
"variable.unglobalize" use

{processorResult: ProcessorResult Ref; cachedGlobalErrorInfoSize: Int32;} () {} [
  cachedGlobalErrorInfoSize: processorResult:;;
  TRUE               @processorResult.!success
  FALSE              @processorResult.!findModuleFail
  FALSE              @processorResult.!passErrorThroughPRE
  String             @processorResult.!program
  ProcessorErrorInfo @processorResult.!errorInfo

  cachedGlobalErrorInfoSize 0 < ~ [
    cachedGlobalErrorInfoSize @processorResult.@globalErrorInfo.shrink
  ] when
] "clearProcessorResult" exportFunction

{processor: Processor Cref; cacheEntry: RefToVar Cref; stackEntry: RefToVar Cref;} Cond {} [
  stackEntry: cacheEntry: processor:;;;

  cacheEntry isGlobal [
    stackEntry isGlobal [
      cacheEntry getVar.globalId
      stackEntry getVar.globalId =
    ] &&
  ] [
    stackEntry isGlobal ~
  ] if
] "variablesHaveSameGlobality" exportFunction

{processor: Processor Cref; checkRefs: Cond; stackDynamicBorder: Nat8; cacheEntry: RefToVar Cref; stackEntry: RefToVar Cref;} Cond {} [
  stackEntry: cacheEntry: stackDynamicBorder: checkRefs: processor:;;;;;

  cacheEntry stackEntry variablesAreSame [cacheEntry stackEntry processor variablesHaveSameGlobality] && [
    cacheEntryVar: cacheEntry getVar;
    stackEntryVar: stackEntry getVar;

    stackEntryVar.data.getTag VarStruct = [
      cacheStruct: VarStruct cacheEntryVar.data.get.get;
      stackStruct: VarStruct stackEntryVar.data.get.get;
      cacheStruct.hasDestructor ~ [cacheStruct.forgotten stackStruct.forgotten =] ||
    ] [
      cacheStaticity: cacheEntry staticityOfVar;
      stackStaticity: stackEntry staticityOfVar;

      cacheStaticity Weak > ~ stackStaticity stackDynamicBorder > ~ and [ # both dynamic
        cacheStaticity Weak > stackStaticity stackDynamicBorder > and [ # both static
          cacheEntry isSemiplainNonrecursiveType [
            result: TRUE;

            cacheEntryVar.data.getTag VarCond VarImport 1 + [
              tag:;
              tag cacheEntryVar.data.get
              tag stackEntryVar.data.get =
              !result
            ] staticCall

            result
          ] [
            cacheEntryVar.data.getTag VarBuiltin = cacheEntryVar.data.getTag VarImport = or [
              [FALSE] "Impossible to create var with builtin or import!" assert
              FALSE
            ] [
              cacheEntryVar.data.getTag VarString = [
                VarString cacheEntryVar.data.get
                VarString stackEntryVar.data.get =
              ] [
                checkRefs [cacheEntryVar.data.getTag VarRef =] && [cacheEntry staticityOfVar Virtual <] && [
                  r1: VarRef cacheEntryVar.data.get.refToVar;
                  r2: VarRef stackEntryVar.data.get.refToVar;
                  r1.var r2.var is [r1.mutable r2.mutable =] && [r1 staticityOfVar r2 staticityOfVar =] &&
                ] [
                  TRUE # go recursive
                ] if
              ] if
            ] if
          ] if
        ] && # both static and are equal
      ] || # both dynamic
    ] if
  ] &&
] "variablesAreEqualWith" exportFunction

{processor: Processor Cref; cacheEntry: RefToVar Cref; stackEntry: RefToVar Cref;} Cond {} [
  stackEntry: cacheEntry: processor:;;;
  stackEntry cacheEntry Weak FALSE processor variablesAreEqualWith
] "variablesAreEqualForMatching" exportFunction

{processor: Processor Cref; cacheEntry: RefToVar Cref; stackEntry: RefToVar Cref;} Cond {} [
  stackEntry: cacheEntry: processor:;;;
  stackEntry cacheEntry Dynamic TRUE processor variablesAreEqualWith
] "variablesAreEqual" exportFunction

{processor: Processor Cref; currentMatchingNode: Block Cref; refToVar: RefToVar Cref;} Cond {} [
  refToVar: currentMatchingNode: processor:;;;
  refToVar getVar.host currentMatchingNode is ~ [refToVar noMatterToCopy ~] &&
] "variableIsUnused" exportFunction

{processor: Processor Cref; nestedToCur: RefToVarTable Ref; curToNested: RefToVarTable Ref; currentMatchingNode: Block Cref; comparingMessage: String Ref; cacheEntry: RefToVar Cref; stackEntry: RefToVar Cref;} Cond {} [
  stackEntry: cacheEntry: comparingMessage: currentMatchingNode: curToNested: nestedToCur: processor:;;;;;;;
  fr1: cacheEntry @nestedToCur.find;

  fr1.success [
    fr1.value stackEntry refsAreEqual [TRUE] [
      currentMatchingNode.nodeCompileOnce ["; aliasing mismatch" @comparingMessage.cat] when
      FALSE
    ] if
  ] [
    fr2: stackEntry @curToNested.find;

    fr2.success [
      fr2.value cacheEntry refsAreEqual [TRUE] [
        currentMatchingNode.nodeCompileOnce ["; aliasing mismatch" @comparingMessage.cat] when
        FALSE
      ] if
    ] [
      cacheEntry.mutable stackEntry.mutable = [
        stackEntry cacheEntry processor variablesAreEqualForMatching [TRUE] [
          currentMatchingNode.nodeCompileOnce ["; static values mismatch" @comparingMessage.cat] when
          FALSE
        ] if
      ] && [
        cacheEntry noMatterToCopy ~ [
          cacheEntry stackEntry @nestedToCur.insert
          stackEntry cacheEntry @curToNested.insert
        ] when

        TRUE
      ] &&
    ] if
  ] if
] "compareOnePair" exportFunction

{
  block: Block Cref;
  processor: Processor Ref;

  comparingMessage: String Ref;
  curToNested: RefToVarTable Ref;
  nestedToCur: RefToVarTable Ref;
  currentMatchingNode: Block Cref;
  cacheEntry: RefToVar Cref;
  stackEntry: RefToVar Cref;
} Cond {} [
  processor: block: ;;
  stackEntry: cacheEntry: currentMatchingNode: nestedToCur: curToNested: comparingMessage:;;;;;;

  overload failProc: @processor block FailProcForProcessor;

  makeWayInfo: [{
    copy currentName:;
    copy current:;
    copy prev:;
  }];

  WayInfo: [
    -1 dynamic -1 dynamic StringView makeWayInfo
  ];

  unfinishedStack: @processor.acquireVarRefArray;
  unfinishedCache: @processor.acquireVarRefArray;
  unfinishedWay: @processor.@unfinishedWay;

  cacheEntry @unfinishedCache.pushBack
  stackEntry @unfinishedStack.pushBack
  WayInfo @unfinishedWay.pushBack

  success: TRUE;

  i: 0 dynamic;
  [
    i unfinishedCache.dataSize < [
      currentFromCache: i unfinishedCache.at copy;
      currentFromStack: i unfinishedStack.at copy;
      currentWay: i unfinishedWay.at copy;

      currentFromCache currentMatchingNode processor variableIsUnused [
        i 1 + !i
      ] [
        currentFromStack currentFromCache @comparingMessage currentMatchingNode @curToNested @nestedToCur processor compareOnePair [ # compare current stack value with initial value of argument
          cacheEntryVar: currentFromCache getVar;
          stackEntryVar: currentFromStack getVar;

          cacheEntryVar.data.getTag VarRef = [currentFromCache staticityOfVar Virtual <] && [currentFromCache staticityOfVar Weak >] && [
            currentFromStack @processor @block getPointeeForMatching @unfinishedStack.pushBack
            currentFromCache @processor @block getPointeeForMatching @unfinishedCache.pushBack
            i -1 "deref" makeStringView makeWayInfo @unfinishedWay.pushBack
          ] [
            cacheEntryVar.data.getTag VarStruct = [
              cacheStruct: VarStruct cacheEntryVar.data.get.get;
              stackStruct: VarStruct stackEntryVar.data.get.get;

              cacheStruct.fields.dataSize stackStruct.fields.dataSize = ~ [
                FALSE !success
              ] [
                j: 0 dynamic;
                [
                  j cacheStruct.fields.dataSize < [
                    cacheFieldNameInfo: j cacheStruct.fields.at.nameInfo;
                    stackFieldNameInfo: j stackStruct.fields.at.nameInfo;

                    cacheFieldNameInfo stackFieldNameInfo = [
                      j currentFromCache @processor block getFieldForMatching @unfinishedCache.pushBack
                      j currentFromStack @processor block getFieldForMatching @unfinishedStack.pushBack
                      i j cacheFieldNameInfo processor.nameManager.getText makeWayInfo @unfinishedWay.pushBack
                      j 1 + !j
                    ] [
                      FALSE !success
                    ] if

                    success copy
                  ] &&
                ] loop
              ] if
            ] [
              # just continue
            ] if
          ] if

          i 1 + @i set
        ] [
          "; way to field: " @comparingMessage.cat
          w: i copy;
          [
            w 0 < ~ [
              curWay:  w unfinishedWay.at;
              curWay.prev unfinishedWay.dataSize < [
                (curWay.current ": " @curWay.@currentName ", " ) @comparingMessage.catMany
                curWay.prev copy !w TRUE
              ] &&
            ] &&
          ] loop

          FALSE !success
        ] if
      ] if

      success copy
    ] &&
  ] loop

  @unfinishedStack @processor.releaseVarRefArray
  @unfinishedCache @processor.releaseVarRefArray
  @unfinishedWay.clear

  success
] "compareEntriesRec" exportFunction

getOverloadIndex: [
  cap: block: file: forMathing: ;;;;
  overloadDepth: cap.nameOverloadDepth copy;
  outOverloadDepth: 0;
  index: -1;

  [
    index file cap.nameInfo processor.nameManager.findItem !index
    index 0 < [
      forMathing ~ [
        ("while matching cant call overload for name: " cap.nameInfo processor.nameManager.getText) assembleString @processor block compilerError
      ] when

      FALSE
    ] [
      overloadDepth 0 = [
        FALSE
      ] [
        oldGnr: cap.nameInfo index @processor @block file getNameWithOverloadIndex;
        oldGnr.startPoint block.id = ~ [outOverloadDepth 1 + !outOverloadDepth] when

        overloadDepth 1 - !overloadDepth
        TRUE
      ] if
    ] if
  ] loop

  index outOverloadDepth
];

tryMatchNode: [
  currentMatchingNode:;

  curToNested: RefToVarTable;
  nestedToCur: RefToVarTable;
  comparingMessage: String;

  canMatch: currentMatchingNode.deleted ~ [
    currentMatchingNode.state NodeStateCompiled =
    currentMatchingNode.state NodeStateFailed = or [
      #recursive condition
      currentMatchingNode.nodeIsRecursive
      [currentMatchingNode.recursionState NodeRecursionStateFail = ~] &&
      [
        currentMatchingNode.state NodeStateNew =
        [currentMatchingNode.state NodeStateHasOutput = [currentMatchingNode.recursionState NodeRecursionStateOld =] &&] ||
        [forceRealFunction copy] ||
      ] &&
    ] ||
    [@processor block getStackDepth currentMatchingNode.matchingInfo.inputs.dataSize currentMatchingNode.matchingInfo.preInputs.dataSize + < ~] &&
    [currentMatchingNode.matchingInfo.hasStackUnderflow ~
      [@processor block getStackDepth currentMatchingNode.matchingInfo.inputs.dataSize currentMatchingNode.matchingInfo.preInputs.dataSize + > ~] ||
    ] &&
  ] &&;

  # matching node has 0 inputs and underflow, current node has 0 inputs - TRUE
  # matching node has 0 inputs and underflow, current node has 1 inputs - FALSE
  # matching node has 0 inputs, current node has 0 inputs - TRUE
  # matching node has 0 inputs, current node has 1 inputs - TRUE

  goodReality:
  forceRealFunction ~ [
    currentMatchingNode.nodeCase NodeCaseDeclaration =
    [currentMatchingNode.nodeCase NodeCaseCodeRefDeclaration =] ||
    [currentMatchingNode.nodeCase NodeCaseExport =] ||
    [currentMatchingNode.nodeCase NodeCaseLambda =] ||
  ] ||;

  invisibleName: currentMatchingNode.nodeCase NodeCaseLambda = [currentMatchingNode.varNameInfo 0 < ~] && [
    matchingCapture: Capture;
    currentMatchingNode.refToVar @matchingCapture.@refToVar set
    NameCaseLocal                @matchingCapture.@captureCase set
    gnr: currentMatchingNode.varNameInfo matchingCapture @processor @block matchingCapture.file getNameForMatching;
    gnr.refToVar.assigned ~
  ] &&;

  canMatch invisibleName ~ and goodReality and [
    mismatchMessage: [
      idadd:;
      msg: makeStringView;
      [
        s: String;
        @msg                        @s.cat
        @idadd call
        " mismatch" makeStringView  @s.cat
        stackEntry.assigned ~ [
          ", stack entry not found" @s.cat
        ] [
          stackEntry cacheEntry variablesAreSame ~ [
            (", stack type is " stackEntry @processor block getMplType ", cache type is " cacheEntry @processor block getMplType) @s.catMany
          ] [
            stackEntry.mutable cacheEntry.mutable = ~ [
              stackEntry.mutable [", stack is mutable" makeStringView] [", stack is immutable" makeStringView] if @s.cat
              cacheEntry.mutable [", cache is mutable" makeStringView] [", cache is immutable" makeStringView] if @s.cat
            ] [
              comparingMessage @s.cat
            ] if
          ] if
        ] if

        (s) addLog
        s @processor block compilerError
      ] call
    ];

    success: TRUE;
    i: 0 dynamic;
    [
      i currentMatchingNode.matchingInfo.inputs.getSize < [
        stackEntry: i @processor block getStackEntry;
        cacheEntry: i currentMatchingNode.matchingInfo.inputs.at.refToVar;

        stackEntry cacheEntry currentMatchingNode @nestedToCur @curToNested @comparingMessage @processor @block compareEntriesRec [
          i 1 + @i set
        ] [
          currentMatchingNode.nodeCompileOnce [
            "in compiled-once func input " [i 1 + @s.cat] mismatchMessage
          ] when

          FALSE dynamic @success set
        ] if

        success processor compilable and
      ] &&
    ] loop

    # calling of pre does not have effect in inputs, but can be used in matching
    success processor compilable and [
      i: 0 dynamic;
      [
        i currentMatchingNode.matchingInfo.preInputs.dataSize < [
          stackEntry: i currentMatchingNode.matchingInfo.inputs.dataSize + @processor block getStackEntry copy;
          cacheEntry: i currentMatchingNode.matchingInfo.preInputs.at;

          cacheEntry.assigned [stackEntry cacheEntry currentMatchingNode @nestedToCur @curToNested @comparingMessage @processor @block compareEntriesRec] && [
            i 1 + @i set
          ] [
            currentMatchingNode.nodeCompileOnce [
              "in compiled-once func preinput " makeStringView [i 1 + @s.cat] mismatchMessage
            ] when

            FALSE dynamic @success set
          ] if

          success processor compilable and
        ] &&
      ] loop
    ] when

    success processor compilable and [
      i: 0 dynamic;
      [
        i currentMatchingNode.matchingInfo.captures.dataSize < [
          currentCapture: i currentMatchingNode.matchingInfo.captures.at;
          cacheEntry: currentCapture.refToVar;
          overloadIndex: outOverloadDepth: currentCapture.refToVar.assigned ~ [-1 -1] [currentCapture @block currentCapture.file TRUE getOverloadIndex] if;;
          stackEntry: currentCapture.nameInfo currentCapture overloadIndex @processor @block currentCapture.file getNameForMatchingWithOverloadIndex.refToVar;

          stackEntry.assigned ~ cacheEntry.assigned ~ and [
            stackEntry.assigned cacheEntry.assigned and [stackEntry cacheEntry currentMatchingNode @nestedToCur @curToNested @comparingMessage @processor @block compareEntriesRec] &&
          ] || [
            i 1 + @i set
          ] [
            currentMatchingNode.nodeCompileOnce [
              "in compiled-once func capture " makeStringView [(currentCapture.nameInfo processor.nameManager.getText "(" currentCapture.nameOverloadDepth ")") @s.catMany] mismatchMessage
            ] when

            FALSE dynamic @success set
          ] if

          success processor compilable and
        ] &&
      ] loop
    ] when

    success processor compilable and [
      i: 0 dynamic;
      [
        i currentMatchingNode.matchingInfo.fieldCaptures.dataSize < [
          currentFieldCapture: i currentMatchingNode.matchingInfo.fieldCaptures.at;
          overloadIndex: outOverloadDepth: currentFieldCapture @block currentFieldCapture.file TRUE getOverloadIndex;;
          processor compilable [
            currentFieldInfo: overloadIndex currentFieldCapture.nameInfo processor.nameManager.getItem;
            currentFieldInfo.nameCase currentFieldCapture.captureCase = [currentFieldCapture.object currentFieldInfo.refToVar variablesAreSame] &&
          ] && [
            i 1 + @i set
          ] [
            currentMatchingNode.nodeCompileOnce [
              ("in compiled-once func fieldCapture " currentFieldCapture.nameInfo processor.nameManager.getText "\" mismatch") assembleString @processor block compilerError
            ] when

            FALSE dynamic @success set
          ] if

          success processor compilable and
        ] &&
      ] loop
    ] when

    success
  ] &&
];

{processor: Processor Ref; block: Block Ref; forceRealFunction: Cond; indexArrayOfSubNode: IndexArray Cref;} Int32 {} [
  processor:;
  block:;

  overload failProc: @processor block FailProcForProcessor;

  forceRealFunction:;
  indexArrayOfSubNode:;

  compileOnce
  indexArrayAddr: indexArrayOfSubNode storageAddress;
  fr: indexArrayAddr @processor.@matchingNodes.find;
  fr.success [
    fr.value.entries 1 + @fr.@value.@entries set

    findInIndexArray: [
      where:;

      result: -1 dynamic;
      i: 0 dynamic;
      [
        i where.dataSize < [
          fr.value.tries 1 + @fr.@value.@tries set
          currentMatchingNodeIndex: i where.at;
          currentMatchingNode: currentMatchingNodeIndex processor.blocks.at.get;

          currentMatchingNode tryMatchNode [
            currentMatchingNodeIndex @result set
            currentMatchingNode.uncompilable ["nested node error" @processor block compilerError] when

            FALSE
          ] [
            i 1 + @i set processor compilable
          ] if
        ] &&
      ] loop

      result
    ];

    result: -1 dynamic;

    @processor block getStackDepth 0 > [
      byType: 0 @processor block getStackEntry getVar.mplSchemaId fr.value.byMplType.find;

      byType.success [
        byType.value findInIndexArray @result set
      ] when
    ] when

    result 0 < [
      fr.value.unknownMplType findInIndexArray @result set
    ] when

    result
  ] [
    -1 dynamic
  ] if

] "tryMatchAllNodesWith" exportFunction

tryMatchAllNodes: [
  processor: block: ;;
  FALSE @block @processor tryMatchAllNodesWith
];

tryMatchAllNodesForRealFunction: [
  processor: block: ;;
  TRUE @block @processor tryMatchAllNodesWith
];

fixRecursionStack: [
  i: block.id copy;
  [
    processor.recursiveNodesStack.getSize 0 > [i newNodeIndex = ~] && [
      current: i @processor.@blocks.at.get;
      i processor.recursiveNodesStack.last = [
        NodeRecursionStateNo @current.@recursionState set
        @processor.@recursiveNodesStack.popBack
      ] when

      current.parent @i set
      [i 0 = ~] "NewNodeIndex is not a parent of block.id while fixRecursionStack!" assert
      TRUE
    ] &&
  ] loop
];

changeNewNodeState: [
  copy newNodeIndex:;
  newNode: newNodeIndex @processor.@blocks.at.get;
  newNode.state NodeStateNew = [
    [newNode.nodeIsRecursive copy] "new node must be recursive!" assert
    fixRecursionStack
    NodeRecursionStateNew @newNode.@recursionState set

    processor.recursiveNodesStack.getSize 0 = [processor.recursiveNodesStack.last newNodeIndex = ~] || [
      newNodeIndex @processor.@recursiveNodesStack.pushBack
    ] when

    NodeStateNoOutput @block.@state set
  ] [
    newNode.state NodeStateNoOutput = [
      NodeStateNoOutput @block.@state set
    ] [
      newNode.recursionState NodeRecursionStateNo > [
        [newNode.nodeIsRecursive copy] "new node must be recursive!" assert
        fixRecursionStack
      ] when

      newNode.recursionState NodeRecursionStateFail > [newNode.state NodeStateHasOutput =] || [NodeStateHasOutput @block.@state set] when
    ] if
  ] if
];

changeNewExportNodeState: [
  copy newNodeIndex:;
  newNode: newNodeIndex @processor.@blocks.at.get;
  newNode.state NodeStateNew = [
    [newNode.nodeIsRecursive copy] "new node must be recursive!" assert
    fixRecursionStack
    NodeRecursionStateNew @newNode.@recursionState set

    processor.recursiveNodesStack.getSize 0 = [processor.recursiveNodesStack.last newNodeIndex = ~] || [
      newNodeIndex @processor.@recursiveNodesStack.pushBack
    ] when

    NodeStateHasOutput @block.@state set
  ] [
    newNode.state NodeStateNoOutput = [
      NodeStateHasOutput @block.@state set
    ] [
      newNode.recursionState NodeRecursionStateNo > [
        [newNode.nodeIsRecursive copy] "new node must be recursive!" assert
        fixRecursionStack
      ] when

      newNode.recursionState NodeRecursionStateFail > [newNode.state NodeStateHasOutput =] || [NodeStateHasOutput @block.@state set] when
    ] if
  ] if
];

fixRef: [
  copy refToVar:;

  var: @refToVar getVar;
  wasVirtual: refToVar isVirtual;
  makeDynamic: FALSE dynamic;
  pointee: VarRef @var.@data.get.@refToVar;
  pointeeVar: pointee getVar;
  pointeeIsLocal: pointeeVar.capturedHead getVar.host currentChangesNode is;

  fixed: pointee copy;
  pointeeIsLocal ~ [ # has shadow - captured from top
    fr: pointeeVar.shadowBegin appliedVars.nestedToCur.find;
    fr.success [
      fr.value @fixed set
    ] [
      # dont have prototype - deref of captured dynamic pointer
      pointee @processor @block copyVarFromChild @fixed set
      TRUE dynamic @makeDynamic set
    ] if
  ] [
    # dont have shadow - to deref of captured dynamic pointer
    # must by dynamic
    var.staticity Static = [pointeeVar.storageStaticity Static =] && ["returning pointer to local variable" @processor block compilerError] when
    pointee @processor @block copyVarFromChild @fixed set
    TRUE dynamic @makeDynamic set
  ] if

  @fixed.var @pointee.setVar

  wasVirtual [@refToVar Virtual @processor block makeStaticity @refToVar set] [
    makeDynamic [
      @refToVar Dynamic @processor block makeStaticity @refToVar set
    ] when
  ] if

  @refToVar
];

applyOnePair: [
  cacheEntry:;
  stackEntry:;

  [
    cacheEntry stackEntry variablesAreSame [TRUE] [
      ("cache type is " makeStringView cacheEntry @processor block getMplType "; stack entry is " makeStringView stackEntry @processor block getMplType) addLog
      FALSE
    ] if
  ] "Applying var has wrong type!" assert
  [cacheEntry noMatterToCopy [cacheEntry getVar.host currentChangesNode is] ||] "Applying unused var!" assert

  cacheEntryVar: cacheEntry  getVar;
  stackEntryVar: @stackEntry getVar;

  @stackEntry cacheEntry staticityOfVar @processor block makeStaticity drop

  cacheEntry noMatterToCopy ~ [cacheEntryVar.shadowEnd getVar.capturedAsMutable copy] && [
    TRUE @stackEntryVar.@capturedAsMutable set
  ] when

  cacheEntry isNonrecursiveType [
    fr: stackEntry @appliedVars.@curToNested.find;
    fr.success [
      fr.value cacheEntry getVar.shadowEnd processor variablesAreEqual ~ [
        "variable changes to incompatible values by two different ways" @processor block compilerError
      ] when
    ] [
      [
        cacheEntry stackEntry processor variablesAreEqualForMatching [
          TRUE
        ] [
          ("match fail, type=" makeStringView cacheEntry @processor block getMplType makeStringView
            "; st=" makeStringView cacheEntry staticityOfVar stackEntry staticityOfVar) addLog
          FALSE
        ] if
      ] "Applying var has wrong value!" assert
      cacheEntry noMatterToCopy ~ [
        [cacheEntryVar.shadowEnd.assigned] "Cache entry has no shadow end!" assert
        stackEntry cacheEntryVar.shadowEnd @appliedVars.@curToNested.insert
        cacheEntry stackEntry @appliedVars.@nestedToCur.insert
      ] when
    ] if
  ] [
    cacheEntryVar.data.getTag VarRef = [
      fr: stackEntry @appliedVars.@curToNested.find;
      fr.success [
        fr.value cacheEntry getVar.shadowEnd processor variablesAreEqual ~ [
          "ref variable changes to incompatible values by two different ways" @processor block compilerError
        ] when
      ] [
        cacheEntry noMatterToCopy ~ [
          [cacheEntryVar.shadowEnd.assigned] "Cache entry has no shadow end!" assert
          stackEntry cacheEntryVar.shadowEnd @appliedVars.@curToNested.insert
          cacheEntry stackEntry @appliedVars.@nestedToCur.insert
        ] when
      ] if
    ] [
      # it may be struct, need add to table anyway for fixing
      cacheEntry noMatterToCopy ~ [
        fr: cacheEntry @appliedVars.@nestedToCur.find;
        fr.success [
          [fr.value stackEntry refsAreEqual] "CacheEntry is already in table with another stackEntry!" assert
        ] [
          cacheEntry stackEntry @appliedVars.@nestedToCur.insert
        ] if
      ] when
    ] if
  ] if
];

applyEntriesRec: [
  cacheEntry:;
  stackEntry:;

  unfinishedStack: @processor.acquireVarRefArray;
  unfinishedCache: @processor.acquireVarRefArray;

  cacheEntry @unfinishedCache.pushBack
  stackEntry @unfinishedStack.pushBack

  i: 0 dynamic;
  [
    i unfinishedCache.dataSize < [
      currentFromCache: i unfinishedCache.at copy;
      currentFromStack: i unfinishedStack.at copy;

      @currentFromStack currentFromCache applyOnePair

      cacheEntryVar: currentFromCache getVar;
      stackEntryVar: currentFromStack getVar;

      cacheEntryVar.capturedAsRealValue [@currentFromStack makeVarRealCaptured] when

      cacheEntryVar.data.getTag VarRef = [currentFromCache staticityOfVar Virtual <] && [currentFromCache staticityOfVar Dynamic >] && [
        clearPointee: VarRef cacheEntryVar.data.get.refToVar copy; # if captured, host index will be currentChangesNodeIndex
        clearPointee getVar.host currentChangesNode is [ # we captured it
          clearPointee @unfinishedCache.pushBack
          @currentFromStack @processor @block getPointeeNoDerefIR @unfinishedStack.pushBack
        ] when
      ] [
        cacheEntryVar.data.getTag VarStruct = [
          cacheStruct: VarStruct cacheEntryVar.data.get.get;

          j: 0 dynamic;
          [
            j cacheStruct.fields.dataSize < [
              cacheFieldRef: j currentFromCache @processor block getFieldForMatching;
              cacheFieldRef getVar.host currentChangesNode is [ # we captured it
                cacheFieldRef @unfinishedCache.pushBack
                j @currentFromStack @processor @block getField @unfinishedStack.pushBack
              ] when
              j 1 + @j set TRUE
            ] &&
          ] loop
        ] when
      ] if

      i 1 + @i set processor compilable
    ] &&
  ] loop

  @unfinishedStack @processor.releaseVarRefArray
  @unfinishedCache @processor.releaseVarRefArray
];

fixOutputRefsRec: [
  stackEntry:;

  unfinishedStack: @processor.acquireVarRefArray;
  stackEntry @unfinishedStack.pushBack

  i: 0 dynamic;
  [
    i unfinishedStack.dataSize < [
      currentFromStack: i @unfinishedStack.at copy;
      stackEntryVar: currentFromStack getVar;

      stackEntryVar.data.getTag VarRef = [
        currentFromStack isSchema ~ [
          stackPointee: VarRef @stackEntryVar.@data.get.refToVar;
          stackPointee getVar.host currentChangesNode is [
            fixed: @currentFromStack fixRef @processor @block getPointeeNoDerefIR;
            fixed @unfinishedStack.pushBack
          ] when
        ] when
      ] [
        stackEntryVar.data.getTag VarStruct = [
          stackStruct: VarStruct stackEntryVar.data.get.get;
          j: 0 dynamic;
          [
            j stackStruct.fields.dataSize < [
              stackField: j stackStruct.fields.at.refToVar;
              stackField @unfinishedStack.pushBack
              j 1 + @j set TRUE
            ] &&
          ] loop
        ] when
      ] if

      i 1 + @i set processor compilable
    ] &&
  ] loop

  @unfinishedStack @processor.releaseVarRefArray
];

fixCaptureRef: [
  refToVar:;
  result: refToVar fixRef;
  fixed: result copy;

  [
    continue: FALSE;
    var: fixed getVar;

    curPointee: VarRef var.data.get.refToVar;
    curPointeeVar: curPointee getVar;

    curPointeeVar.data.getTag VarRef = [
      fr: curPointee @appliedVars.@curToNested.find;
      fr.success ~ [
        curPointee fixRef @fixed set
        TRUE dynamic @continue set
        # we need deep recursion for captures, becouse if we has dynamic fix to, we will has unfixed pointee
        # need to fix!!!
      ] when
    ] when

    continue
  ] loop

  result
];

usePreCapturesWith: [
  compileOnce
  copy exitPre:;
  currentChangesNodeIndex:;
  currentChangesNodeIndex 0 < ~ [
    currentChangesNode: currentChangesNodeIndex processor.blocks.at.get;

    oldSuccess: @processor.@result move copy;
    -1 @processor.@result clearProcessorResult

    i: 0 dynamic;
    [
      i currentChangesNode.matchingInfo.captures.dataSize < [
        currentCapture: i currentChangesNode.matchingInfo.captures.at;
        cacheEntry: currentCapture.refToVar;
        overloadIndex: outOverloadDepth: currentCapture.refToVar.assigned ~ [-1 -1] [currentCapture @block currentCapture.file TRUE getOverloadIndex] if;;
        gnr: currentCapture.nameInfo currentCapture overloadIndex @processor @block currentCapture.file getNameForMatchingWithOverloadIndex;
        gnr.refToVar.assigned ~ [
          # it is failed capture
        ] [
          stackEntry: @gnr outOverloadDepth @processor @block currentCapture.file captureName.refToVar;

          unfinishedStack: @processor.acquireVarRefArray;
          unfinishedCache: @processor.acquireVarRefArray;
          cacheEntry @unfinishedCache.pushBack
          stackEntry @unfinishedStack.pushBack
          i2: 0 dynamic;
          [
            i2 unfinishedCache.getSize < [
              currentFromCache: i2 unfinishedCache.at copy;
              currentFromStack: i2 unfinishedStack.at copy;
              cacheEntryVar: currentFromCache getVar;
              stackEntryVar: currentFromStack getVar;

              cacheEntryVar.data.getTag VarRef = [currentFromCache staticityOfVar Virtual <] && [currentFromCache staticityOfVar Dynamic >] && [
                clearPointee: VarRef cacheEntryVar.data.get.refToVar copy; # if captured, host index will be currentChangesNodeIndex
                clearPointee getVar.host currentChangesNode is [ # we captured it
                  clearPointee                                            @unfinishedCache.pushBack
                  @currentFromStack @processor @block getPointeeNoDerefIR @unfinishedStack.pushBack
                ] when
              ] [
                cacheEntryVar.data.getTag VarStruct = [
                  cacheStruct: VarStruct cacheEntryVar.data.get.get;

                  j: 0 dynamic;
                  [
                    j cacheStruct.fields.dataSize < [
                      cacheFieldRef: j currentFromCache @processor block getFieldForMatching;
                      cacheFieldRef getVar.host currentChangesNode is [ # we captured it
                        cacheFieldRef @unfinishedCache.pushBack
                        j @currentFromStack @processor @block getField @unfinishedStack.pushBack
                      ] when
                      j 1 + @j set processor compilable
                    ] &&
                  ] loop
                ] when
              ] if

              i2 1 + @i2 set processor compilable
            ] &&
          ] loop

          @unfinishedStack @processor.releaseVarRefArray
          @unfinishedCache @processor.releaseVarRefArray
        ] if

        i 1 + @i set processor compilable
      ] &&
    ] loop

    i: 0 dynamic;
    [
      i currentChangesNode.matchingInfo.fieldCaptures.dataSize < [
        currentFieldCapture: i currentChangesNode.matchingInfo.fieldCaptures.at;
        overloadIndex: outOverloadDepth: currentFieldCapture @block currentFieldCapture.file TRUE getOverloadIndex;;
        fieldCnr: currentFieldCapture.nameInfo overloadIndex @processor @block currentFieldCapture.file getNameWithOverloadIndex outOverloadDepth @processor @block currentFieldCapture.file captureName;
        i 1 + @i set processor compilable
      ] &&
    ] loop

    exitPre ~ [
      currentChangesNode.matchingInfo.unfoundedNames [
        un: .key;
        un.file un.nameInfo 0 @processor @block addUnfoundedName
      ] each
    ] when

    @oldSuccess move @processor.@result set
  ] when
];

usePreCaptures: [FALSE dynamic usePreCapturesWith];

addFailedCapture: [
  nameInfo:;
  file:;

  newCapture: Capture;
  nameInfo @newCapture.@nameInfo set
  file     @newCapture.@file.set

  newCapture @block.@matchingInfo.@captures.pushBack
  block.state NodeStateNew = [
    newCapture @block.@buildingMatchingInfo.@captures.pushBack
  ] when

  file nameInfo 0 @processor @block addEmptyCapture
];

applyNodeChanges: [
  compileOnce
  copy currentChangesNodeIndex:;
  currentChangesNode: currentChangesNodeIndex processor.blocks.at.get;

  [@processor block getStackDepth currentChangesNode.matchingInfo.inputs.dataSize < ~] "Stack underflow!" assert

  appliedVars: {
    curToNested: RefToVarTable;
    nestedToCur: RefToVarTable;
    fixedOutputs: @processor.acquireVarRefArray;
  };

  pops: @processor.acquireVarRefArray;

  i: 0 dynamic;
  [
    i currentChangesNode.matchingInfo.inputs.dataSize < [
      stackEntry: @processor @block popForMatching;
      cacheEntry: i currentChangesNode.matchingInfo.inputs.at.refToVar;

      stackEntry cacheEntry applyEntriesRec
      stackEntry @pops.pushBack

      i 1 + @i set processor compilable
    ] &&
  ] loop

  i: 0 dynamic;
  [
    i pops.dataSize < [
      pops.dataSize i - 1 - pops.at @block push
      i 1 + @i set processor compilable
    ] &&
  ] loop

  i: 0 dynamic;
  [
    i currentChangesNode.matchingInfo.captures.dataSize < [
      currentCapture: i currentChangesNode.matchingInfo.captures.at;

      cacheEntry: currentCapture.refToVar;
      cacheEntry.assigned ~ [
        currentCapture.file currentCapture.nameInfo addFailedCapture
      ] [
        overloadIndex: outOverloadDepth: currentCapture @block currentCapture.file FALSE getOverloadIndex ;;
        gnr: currentCapture.nameInfo currentCapture overloadIndex @processor @block currentCapture.file getNameForMatchingWithOverloadIndex;
        [gnr.refToVar.assigned] "Stack entry not found!" assert
        stackEntry: gnr outOverloadDepth @processor @block currentCapture.file captureName.refToVar;
        stackEntry cacheEntry applyEntriesRec
      ] if

      i 1 + @i set processor compilable
    ] &&
  ] loop

  i: 0 dynamic;
  [
    i currentChangesNode.matchingInfo.fieldCaptures.dataSize < [
      currentFieldCapture: i currentChangesNode.matchingInfo.fieldCaptures.at;
      overloadIndex: outOverloadDepth: currentFieldCapture @block currentFieldCapture.file FALSE getOverloadIndex;;
      fieldCnr: currentFieldCapture.nameInfo overloadIndex @processor @block currentFieldCapture.file getNameWithOverloadIndex outOverloadDepth @processor @block currentFieldCapture.file captureName;

      i 1 + @i set processor compilable
    ] &&
  ] loop

  i: 0 dynamic;
  [
    i currentChangesNode.outputs.dataSize < [
      currentOutput: i currentChangesNode.outputs.at;
      outputRef: currentOutput.refToVar @processor @block copyVarFromChild; # output is to inner var
      outputRef fixOutputRefsRec
      outputRef @appliedVars.@fixedOutputs.pushBack
      i 1 + @i set processor compilable
    ] &&
  ] loop

  appliedVars.curToNested [
    pair:;
    pair.value pair.key @appliedVars.@nestedToCur.insert
  ] each

  @appliedVars.@curToNested [
    pair:;
    curVar:    pair.key getVar;
    nestedVar: pair.value getVar;
    nestedVar.data.getTag VarRef = [
      nestedCopy: pair.value @processor @block copyOneVar;
      pair.value isGlobal [
        pVar: pair.value  getVar;
        nVar: @nestedCopy getVar;
        pVar.globalId @nVar.@globalId set
      ] when
      nestedCopy fixCaptureRef @pair.@value set
    ] when
  ] each

  @pops @processor.releaseVarRefArray

  @appliedVars
];

changeVarValue: [
  dst:;
  src:;

  processor compilable [
    varSrc: src  getVar;
    varDst: @dst getVar;

    varSrc.staticity @varDst.@staticity set
    dst isNonrecursiveType [
      varDst.data.getTag VarCond VarString 1 + [
        copy tag:;
        srcBranch: tag varSrc.data.get;
        dstBranch: tag @varDst.@data.get;
        srcBranch @dstBranch set
      ] staticCall
    ] [
      varDst.data.getTag VarRef = [
        srcBranch: VarRef varSrc.data.get;
        dstBranch: VarRef @varDst.@data.get;
        srcBranch @dstBranch set
      ] when
    ] if
  ] when
];

usePreInputsWith: [
  copy exitPre:;
  newNodeIndex:;
  newNodeIndex 0 < ~ [
    newNode: newNodeIndex processor.blocks.at.get;

    newMinStackDepth: @processor block getStackDepth newNode.matchingInfo.inputs.dataSize - newNode.matchingInfo.preInputs.dataSize -;
    newMinStackDepth block.minStackDepth < [
      newMinStackDepth @block.@minStackDepth set
    ] when

    exitPre ~ [
      newNode.matchingInfo.hasStackUnderflow [
        @block addStackUnderflowInfo
      ] when
    ] when
  ] when
];

usePreInputs: [FALSE dynamic usePreInputsWith];

isImplicitDeref: [
  copy case:;
  case ArgReturnDeref =
  case ArgRefDeref = or
];

derefNEntries: [
  implicitDerefInfo: count: block:;;;
  i: 0 dynamic;
  [
    i count < [
      count 1 - i - implicitDerefInfo.at [
        dst: i @processor @block getStackEntry;
        @dst @processor @block getPossiblePointee @dst set
      ] when
      i 1 + @i set TRUE
    ] &&
  ] loop
];

applyNamedStackChanges: [
  forcedName:;
  appliedVars:;
  copy currentChangesNodeIndex:;
  newNode:;
  compileOnce

  currentChangesNodeIndex usePreInputs

  inputs: @processor.acquireVarRefArray;
  outputs: @processor.acquireVarRefArray;

  i: 0 dynamic;
  [
    i newNode.matchingInfo.inputs.dataSize < [
      @processor @block pop @inputs.pushBack
      i 1 + @i set TRUE
    ] &&
  ] loop

  i: 0 dynamic;
  [
    i appliedVars.fixedOutputs.getSize < [
      outputRef: i @appliedVars.@fixedOutputs.at;
      outputRef @outputs.pushBack
      outputRef getVar.data.getTag VarStruct = [
        @outputRef markAsAbleToDie
        outputRef @block.@candidatesToDie.pushBack
      ] when
      outputRef @block push
      i 1 + @i set TRUE
    ] &&
  ] loop

  processor compilable [
    inputs @outputs newNode forcedName makeNamedCallInstruction

    implicitDerefInfo: @processor.@condArray;
    newNode.outputs [.argCase isImplicitDeref @implicitDerefInfo.pushBack] each
    implicitDerefInfo appliedVars.fixedOutputs.getSize @block derefNEntries
    @implicitDerefInfo.clear
  ] when

  @inputs @processor.releaseVarRefArray
  @outputs @processor.releaseVarRefArray
];

applyStackChanges: [
  forcedName: StringView dynamic;
  forcedName applyNamedStackChanges
];

makeCallInstructionWith: [
  block:;
  copy dynamicFunc:;
  refToVar:;
  forcedName:;
  newNode:;
  outputs:;
  inputs:;
  argRet: RefToVar;
  argList: @processor.@irArgumentArray;

  [newNode.variadic [inputs.getSize newNode.matchingInfo.inputs.getSize =] ||] "Input count mismatch!" assert

  i: 0 dynamic;
  [
    i inputs.getSize < [
      currentInputArgCase: i newNode.matchingInfo.inputs.getSize < [
        i newNode.matchingInfo.inputs.at.argCase copy
      ] [
        ArgCopy
      ] if;

      currentInput: i inputs.at;

      currentInputArgCase ArgVirtual = [currentInputArgCase ArgGlobal =] || [
      ] [
        arg: IRArgument;
        currentInput getVar.irNameId @arg.@irNameId set
        currentInput @processor getMplSchema.irTypeId @arg.@irTypeId set
        currentInputArgCase ArgRef = [currentInputArgCase ArgRefDeref =] || @arg.@byRef set
        currentInputArgCase ArgCopy = [currentInput @processor @block createDerefToRegister @arg.@irNameId set] when

        arg @argList.pushBack
      ] if

      i 1 + @i set TRUE
    ] &&
  ] loop

  i: 0 dynamic;
  [
    i newNode.outputs.dataSize < [
      currentOutput: i newNode.outputs.at;
      outputRef: i @outputs.at; # output is to inner var

      currentOutput.argCase ArgVirtual = [
      ] [
        refToVar: outputRef;
        outputRef getVar.allocationInstructionIndex 0 <
        [outputRef getVar.globalDeclarationInstructionIndex 0 <] && [
          @outputRef @processor @block createAllocIR r:;
        ] when

        currentOutput.argCase ArgReturn = [currentOutput.argCase ArgReturnDeref =] || [
          refToVar @argRet set
        ] [
          arg: IRArgument;
          refToVar getVar.irNameId @arg.@irNameId set
          refToVar @processor getMplSchema.irTypeId @arg.@irTypeId set
          TRUE @arg.@byRef set

          arg @argList.pushBack
        ] if
      ] if

      i 1 + @i set TRUE
    ] &&
  ] loop

  i: 0 dynamic;
  [
    i newNode.matchingInfo.captures.dataSize < [
      currentCapture: i newNode.matchingInfo.captures.at;

      currentCapture.refToVar.assigned [
        currentCapture.argCase ArgRef = [
          overloadIndex: outOverloadDepth: currentCapture @block currentCapture.file FALSE getOverloadIndex;;
          refToVar: currentCapture.nameInfo currentCapture overloadIndex @processor @block currentCapture.file getNameForMatchingWithOverloadIndex outOverloadDepth @processor @block currentCapture.file captureName.refToVar;
          [currentCapture.refToVar refToVar variablesAreSame] "invalid capture type while generating arg list!" assert

          arg: IRArgument;
          refToVar getVar.irNameId @arg.@irNameId set
          refToVar @processor getMplSchema.irTypeId @arg.@irTypeId set
          TRUE @arg.@byRef set
          TRUE @arg.@byRef set

          arg @argList.pushBack
        ] when
      ] when

      i 1 + @i set TRUE
    ] &&
  ] loop

  newNode.empty ~ [
    pureFuncName: forcedName "" = [dynamicFunc [refToVar @processor getIrName][newNode.irName makeStringView] if][forcedName copy] if;
    funcName: newNode.variadic [("(" newNode.argTypes ") " pureFuncName) assembleString][pureFuncName toString] if;
    convName: newNode.convention;
    retName: argRet argList convName funcName @processor @block createCallIR;

    argRet.var isNil ~ [
      @retName argRet @processor @block createStoreFromRegister
    ] when
  ] when

  @argList.clear
];

makeNamedCallInstruction: [
  r: RefToVar;
  r FALSE dynamic @block makeCallInstructionWith
];

makeCallInstruction: [
  r: RefToVar;
  forcedName: StringView;
  forcedName r FALSE dynamic @block makeCallInstructionWith
];

processNamedCallByNode: [
  forcedName:;
  copy newNodeIndex:;
  newNode: newNodeIndex processor.blocks.at.get;
  compileOnce

  newNodeIndex changeNewNodeState
  newNode.state NodeStateNoOutput = ~ [
    appliedVars: newNodeIndex applyNodeChanges;

    appliedVars.curToNested [
      pair:;
      pair.value pair.key copy changeVarValue
    ] each

    newNode newNodeIndex @appliedVars forcedName applyNamedStackChanges

    @appliedVars.@fixedOutputs @processor.releaseVarRefArray
  ] when
];

processCallByNode: [
  forcedName: StringView dynamic;
  forcedName processNamedCallByNode
];

{block: Block Ref; processor: Processor Ref;
  positionInfo: CompilerPositionInfo Cref; name: StringView Cref; nodeCase: NodeCaseCode; indexArray: IndexArray Cref;} () {} [
  block:;
  processor:;
  positionInfo:;
  name:;
  copy nodeCase:;
  indexArray:;

  overload failProc: @processor block FailProcForProcessor;

  forcedNameString: String;
  file: positionInfo.file;

  newNodeIndex: indexArray @processor @block tryMatchAllNodes;
  newNodeIndex 0 < [processor compilable] && [
    name
    block.id
    nodeCase
    indexArray
    file
    positionInfo
    CFunctionSignature
    @processor
    astNodeToCodeNode @newNodeIndex set
  ] when

  processor compilable [
    newNode: newNodeIndex @processor.@blocks.at.get;
    block.parent 0 = [nodeCase NodeCaseList = nodeCase NodeCaseObject = or] && [newNode.matchingInfo.inputs.getSize 0 =] && [newNode.outputs.getSize 1 =] && [
      realCapturesCount: 0;
      newNode.matchingInfo.captures [
        capture:;
        capture.refToVar.assigned [
          capture.refToVar isVirtual ~ [realCapturesCount 1 + @realCapturesCount set] when
        ] when
      ] each

      realCapturesCount 0 =
    ] && [
      0 newNode.outputs.at.refToVar isStaticData
    ] && [
      result: 0 newNode.outputs.at.refToVar @processor @block copyVarFromChild;
      TRUE @newNode.@deleted set
      @result @processor @block createStaticInitIR @block push
    ] [
      forcedName: forcedNameString makeStringView;
      newNodeIndex forcedName processNamedCallByNode
    ] if
  ] [
    newNodeIndex usePreInputs
    newNodeIndex usePreCaptures
  ] if
] "processCallByIndexArray" exportFunction

{block: Block Ref; processor: Processor Ref; name: StringView Cref; file: File Cref; callAstNodeIndex: Int32;} () {} [
  block:;
  processor:;
  name:;
  file:;
  callAstNodeIndex:;
  overload failProc: @processor block FailProcForProcessor;

  astNode: callAstNodeIndex processor.multiParserResult.memory.at;

  positionInfo: astNode file makeCompilerPosition;

  indexArray: Int32 Array Cref;
  nodeCase: Nat8;
  (
    AstNodeType.Code   [!indexArray NodeCaseCode   !nodeCase]
    AstNodeType.List   [!indexArray NodeCaseList   !nodeCase]
    AstNodeType.Object [!indexArray NodeCaseObject !nodeCase]
  ) astNode.data.visit

  indexArray nodeCase dynamic name positionInfo @processor @block processCallByIndexArray
] "processCall" exportFunction

{block: Block Ref; processor: Processor Ref; file: File Cref; preAstNodeIndex: Int32;} Cond {} [
  block:;
  processor:;
  file:;
  preAstNodeIndex:;
  overload failProc: @processor block FailProcForProcessor;

  processor compilable [
    astNode: preAstNodeIndex processor.multiParserResult.memory.at;
    positionInfo: astNode file makeCompilerPosition;
    indexArray: AstNodeType.Code @astNode.@data.get;

    oldSuccess: processor compilable;
    oldGlobalErrorCount: processor.result.globalErrorInfo.getSize;

    newNodeIndex: indexArray @processor @block tryMatchAllNodes;
    newNodeIndex 0 < [processor compilable] && [
      processor.depthOfPre 1 + @processor.@depthOfPre set
      "PRE" makeStringView block.id NodeCaseCode indexArray file positionInfo CFunctionSignature @processor astNodeToCodeNode @newNodeIndex set
      processor.depthOfPre 1 - @processor.@depthOfPre set
    ] when

    oldGlobalErrorCount @processor.@result.@globalErrorInfo.shrink
    oldSuccess [
      processor.@result.passErrorThroughPRE ~ [-1 @processor.@result clearProcessorResult] when
    ] [
      [FALSE] "Has compilerError before trying compiling pre!" assert
    ] if

    newNode: newNodeIndex processor.blocks.at.get;
    newNodeIndex TRUE dynamic usePreInputsWith
    newNodeIndex TRUE dynamic usePreCapturesWith

    newNode.matchingInfo.hasStackUnderflow [
      block.minStackDepth 1 - @block.@minStackDepth set
    ] when

    newNode.matchingInfo.unfoundedNames [
      un: .key;
      un.file un.nameInfo addFailedCapture
    ] each

    newNode.uncompilable ~
    [newNode.outputs.dataSize 0 >] &&
    [
      top: newNode.outputs.last.refToVar;
      top getVar.data.getTag VarCond =
      [top staticityOfVar Weak < ~] && [
        VarCond top getVar.data.get copy
      ] [
        TRUE dynamic @processor.@result.@passErrorThroughPRE set
        "PRE code must fail or return static Cond" @processor block compilerError
        FALSE dynamic
      ] if
    ] &&
  ] [
    FALSE dynamic
  ] if
] "processPre" exportFunction

processIf: [
  processor: block: ;;

  fileElse:;
  astNodeElse:;
  fileThen:;
  astNodeThen:;
  refToCond:;

  indexArrayElse: AstNodeType.Code astNodeElse.data.get;
  indexArrayThen: AstNodeType.Code astNodeThen.data.get;

  positionInfoThen: astNodeThen fileThen makeCompilerPosition;
  positionInfoElse: astNodeElse fileElse makeCompilerPosition;

  newNodeThenIndex: @indexArrayThen @processor @block tryMatchAllNodes;
  newNodeThenIndex 0 < [processor compilable] && [
    "ifThen" makeStringView
    block.id
    NodeCaseCode
    indexArrayThen
    fileThen
    positionInfoThen
    CFunctionSignature
    @processor astNodeToCodeNode @newNodeThenIndex set
  ] when

  newNodeThenIndex usePreInputs

  processor compilable [
    newNodeThen: newNodeThenIndex @processor.@blocks.at.get;
    newNodeElseIndex: @indexArrayElse @processor @block tryMatchAllNodes;
    newNodeElseIndex 0 < [processor compilable] && [
      "ifElse" makeStringView
      block.id
      NodeCaseCode
      indexArrayElse
      fileElse
      positionInfoElse
      CFunctionSignature
      @processor
      astNodeToCodeNode @newNodeElseIndex set
    ] when

    newNodeElseIndex usePreInputs

    processor compilable [
      newNodeElse: newNodeElseIndex @processor.@blocks.at.get;

      newNodeThenIndex changeNewNodeState
      newNodeElseIndex changeNewNodeState

      newNodeThen.state NodeStateHasOutput < [newNodeElse.state NodeStateHasOutput <] || [
        #merging uncompiled nodes
        newNodeThen.state NodeStateHasOutput < [newNodeElse.state NodeStateHasOutput <] && [
          NodeStateNoOutput @block.@state set
        ] [
          newNodeThen.state NodeStateHasOutput < [
            newNodeElseIndex processCallByNode
          ] [
            newNodeThenIndex processCallByNode
          ] if

          NodeStateHasOutput @block.@state set
        ] if
      ] [
        newNodeThen.state NodeStateHasOutput = [newNodeElse.state NodeStateHasOutput =] || [NodeStateHasOutput @block.@state set] when

        appliedVarsThen: newNodeThenIndex applyNodeChanges;
        appliedVarsElse: newNodeElseIndex applyNodeChanges;

        stackDepth: @processor block getStackDepth;
        newNodeThen.matchingInfo.inputs.dataSize stackDepth > ["then branch stack underflow" @processor block compilerError] when
        newNodeElse.matchingInfo.inputs.dataSize stackDepth > ["else branch stack underflow" @processor block compilerError] when
        stackDepth newNodeThen.matchingInfo.inputs.dataSize - newNodeThen.outputs.dataSize +
        stackDepth newNodeElse.matchingInfo.inputs.dataSize - newNodeElse.outputs.dataSize + = ~ ["if branches stack size mismatch" @processor block compilerError] when

        processor compilable [
          longestInputSize: newNodeThen.matchingInfo.inputs.dataSize copy;
          newNodeElse.matchingInfo.inputs.dataSize longestInputSize > [newNodeElse.matchingInfo.inputs.dataSize @longestInputSize set] when
          longestOutputSize: newNodeThen.outputs.dataSize copy;
          newNodeElse.outputs.dataSize longestOutputSize > [newNodeElse.outputs.dataSize @longestOutputSize set] when
          shortestInputSize: newNodeThen.matchingInfo.inputs.dataSize newNodeElse.matchingInfo.inputs.dataSize + longestInputSize -;
          shortestOutputSize: newNodeThen.outputs.dataSize newNodeElse.outputs.dataSize + longestOutputSize -;

          getOutput: [
            branch:;
            copy index:;
            index branch.fixedOutputs.dataSize + longestOutputSize < [
              longestInputSize index - 1 - @processor block getStackEntry copy
            ] [
              index branch.fixedOutputs.dataSize + longestOutputSize - branch.fixedOutputs.at copy
            ] if
          ];

          isOutputImplicitDeref: [
            branch:;
            copy index:;
            index branch.outputs.dataSize + longestOutputSize < [
              FALSE
            ] [
              index branch.outputs.dataSize + longestOutputSize - branch.outputs.at.argCase isImplicitDeref
            ] if
          ];

          getCompiledInput: [
            compiledOutputs:;
            branch:;
            copy index:;

            index branch.outputs.dataSize + longestOutputSize < [
              longestInputSize 1 - i - inputs.at copy
            ] [
              index branch.outputs.dataSize + longestOutputSize - compiledOutputs.at copy
            ] if
          ];

          getCompiledOutput: [
            compiledOutputs:;
            branch:;
            copy index:;
            index branch.outputs.dataSize + longestOutputSize < [
              index outputs.at
            ] [
              index branch.outputs.dataSize + longestOutputSize - compiledOutputs.at
            ] if
          ];

          # merge captures
          mergeValues: [
            refToDst:;
            value2:;
            value1:;

            [value1 value2 variablesAreSame] "captures changed to different types!" assert
            value1 staticityOfVar Dynamic = value2 staticityOfVar Dynamic = or [
              @refToDst @processor @block makeVarDynamic
              @value1 @processor @block makePointeeDirtyIfRef
              @value2 @processor @block makePointeeDirtyIfRef
            ] [
              value1 value2 processor variablesAreEqual [ # both are static, same value
                value1 @refToDst changeVarValue
              ] [
                @refToDst @processor @block makeVarDynamic
                @value1 @processor @block makePointeeDirtyIfRef
                @value2 @processor @block makePointeeDirtyIfRef
              ] if
            ] if
          ];

          mergeValuesRec: [
            refToDst:;
            value2:;
            value1:;

            unfinishedV1: @processor.acquireVarRefArray;
            unfinishedV2: @processor.acquireVarRefArray;
            unfinishedD:  @processor.acquireVarRefArray;

            value1   @unfinishedV1.pushBack
            value2   @unfinishedV2.pushBack
            refToDst @unfinishedD .pushBack

            [
              unfinishedD.dataSize 0 > [
                lastD: unfinishedD.last copy;
                lastV1: unfinishedV1.last copy;
                lastV2: unfinishedV2.last copy;
                @unfinishedD.popBack
                @unfinishedV1.popBack
                @unfinishedV2.popBack

                @lastV1 @lastV2 @lastD mergeValues

                lastD getVar.data.getTag VarStruct = [
                  [lastV1 getVar.data.getTag VarStruct =] "Merging structures type fail!" assert
                  [lastV2 getVar.data.getTag VarStruct =] "Merging structures type fail!" assert
                  structD: VarStruct lastD getVar.data.get.get;
                  structV1: VarStruct lastV1 getVar.data.get.get;
                  structV2: VarStruct lastV2 getVar.data.get.get;
                  [structD.fields.dataSize structV1.fields.dataSize =] "Merging structures fieldCount fail!" assert
                  [structD.fields.dataSize structV2.fields.dataSize =] "Merging structures fieldCount fail!" assert
                  f: 0;
                  [
                    f structD.fields.dataSize < [
                      f structV1.fields.at.refToVar @unfinishedV1.pushBack
                      f structV2.fields.at.refToVar @unfinishedV2.pushBack
                      f structD .fields.at.refToVar @unfinishedD .pushBack
                      f 1 + @f set TRUE
                    ] &&
                  ] loop
                ] when

                TRUE
              ] &&
            ] loop

            @unfinishedV1 @processor.releaseVarRefArray
            @unfinishedV2 @processor.releaseVarRefArray
            @unfinishedD  @processor.releaseVarRefArray
          ];

          @appliedVarsThen.@curToNested [
            pair:;
            fr: pair.key @appliedVarsElse.@curToNested.find;
            fr.success [
              @pair.@value @fr.@value pair.key copy mergeValues
            ] [
              @pair.@value pair.key copy pair.key copy mergeValues
            ] if
          ] each

          @appliedVarsElse.@curToNested [
            pair:;
            fr: pair.key @appliedVarsThen.@curToNested.find;
            fr.success [
              # capture changed in both branches, we just applied it
            ] [
              @pair.@value pair.key copy pair.key copy mergeValues
            ] if
          ] each

          # check stack consistency
          inputsThen:  @processor.acquireVarRefArray;
          inputsElse:  @processor.acquireVarRefArray;
          outputsThen: @processor.acquireVarRefArray;
          outputsElse: @processor.acquireVarRefArray;
          inputs:      @processor.acquireVarRefArray;
          outputs:     @processor.acquireVarRefArray;

          implicitDerefInfo: @processor.@condArray;

          i: 0 dynamic;
          [
            i longestOutputSize < [
              outputThen: i appliedVarsThen getOutput;
              outputElse: i appliedVarsElse getOutput;
              isOutputImplicitDerefThen: i newNodeThen isOutputImplicitDeref;
              isOutputImplicitDerefElse: i newNodeElse isOutputImplicitDeref;

              isOutputImplicitDerefThen isOutputImplicitDerefElse = [
                outputThen outputElse variablesAreSame [
                  newOutput: outputThen copy;
                  outputElse.mutable outputThen.mutable and @newOutput.setMutable
                  outputThen outputElse newOutput mergeValuesRec
                  i newNodeThen.outputs.dataSize + longestOutputSize < ~ [newOutput @outputsThen.pushBack] when
                  i newNodeElse.outputs.dataSize + longestOutputSize < ~ [newOutput @outputsElse.pushBack] when
                  @newOutput @processor @block createAllocIR @outputs.pushBack
                ] [
                  ("branch types mismatch; in 'then' type is " outputThen @processor block getMplType "; in 'else' type is " outputElse @processor block getMplType) assembleString @processor block compilerError
                ] if

                isOutputImplicitDerefThen @implicitDerefInfo.pushBack
              ] [
                "branch return cases mismatch" @processor block compilerError
              ] if

              i 1 + @i set processor compilable
            ] &&
          ] loop

          processor compilable [
            i: 0 dynamic;
            [
              i longestInputSize < [
                a: @processor @block pop;
                a @inputs.pushBack
                i newNodeThen.matchingInfo.inputs.dataSize < [a @inputsThen.pushBack] when
                i newNodeElse.matchingInfo.inputs.dataSize < [a @inputsElse.pushBack] when
                i 1 + @i set TRUE
              ] &&
            ] loop

            i: 0 dynamic;
            [
              i outputs.dataSize < [
                outputRef: i @outputs.at;
                outputRef getVar.data.getTag VarStruct = [
                  @outputRef markAsAbleToDie
                  outputRef @block.@candidatesToDie.pushBack
                ] when

                outputRef @block push
                i 1 + @i set TRUE
              ] &&
            ] loop

            processor compilable [
              # create instruction
              #1 prolog, allocate common vars

              createStores: [
                compiledOutputs:;
                branch:;

                i: 0 dynamic;
                [
                  i longestOutputSize < [
                    current: i branch compiledOutputs getCompiledOutput;
                    curInput: i branch compiledOutputs getCompiledInput;

                    current.var curInput.var is ~ [
                      curInput isVirtual ~ ["variable states in branches mismatch" @processor block compilerError] when
                      FALSE @curInput getVar.@temporary set
                      current @curInput @processor @block createCheckedCopyToNewNoDie
                    ] when

                    i 1 + @i set TRUE
                  ] &&
                ] loop
              ];

              wasNestedCall: block.hasNestedCall copy;
              0 refToCond @processor @block createBranch
              @block createLabel
              inputsThen @outputsThen newNodeThen makeCallInstruction
              newNodeThen outputsThen createStores
              0 @block createJump
              @block createLabel
              wasNestedCall @block.@hasNestedCall set
              inputsElse @outputsElse newNodeElse makeCallInstruction
              newNodeElse outputsElse createStores
              1 @block createJump
              @block createLabel
              implicitDerefInfo longestOutputSize @block derefNEntries
              processor.options.verboseIR ["create phi nodes..." @block createComment] when
              processor.options.verboseIR ["end if" @block createComment] when
            ] when
          ] when

          @inputsThen  @processor.releaseVarRefArray
          @inputsElse  @processor.releaseVarRefArray
          @outputsThen @processor.releaseVarRefArray
          @outputsElse @processor.releaseVarRefArray
          @inputs      @processor.releaseVarRefArray
          @outputs     @processor.releaseVarRefArray

          @implicitDerefInfo.clear
        ] when

        @appliedVarsThen.@fixedOutputs @processor.releaseVarRefArray
        @appliedVarsElse.@fixedOutputs @processor.releaseVarRefArray
      ] if
    ] when
  ] when
];

processLoop: [
  astNode: processor: block: file: ;;;;
  indexArray: AstNodeType.Code astNode.data.get;
  positionInfo: astNode file makeCompilerPosition;

  iterationNumber: 0 dynamic;
  loopIsDynamic: FALSE;

  [
    newNodeIndex: @indexArray @processor @block tryMatchAllNodes;
    newNodeIndex 0 < [processor compilable] && [
      "loop" makeStringView
      block.id
      NodeCaseCode
      indexArray
      file
      positionInfo
      CFunctionSignature
      @processor
      astNodeToCodeNode @newNodeIndex set
    ] when

    newNodeIndex usePreInputs

    processor compilable [
      newNode: newNodeIndex @processor.@blocks.at.get;
      newNodeIndex changeNewNodeState

      newNode.state NodeStateHasOutput < [
        FALSE
      ] [
        newNode.state NodeStateHasOutput = [NodeStateHasOutput @block.@state set] when
        appliedVars: newNodeIndex applyNodeChanges;

        appliedVars.fixedOutputs.getSize 0 = ["loop body must return Cond" @processor block compilerError] when
        processor compilable [
          condition: newNode.outputs.last.refToVar;
          condVar: condition getVar;
          condVar.data.getTag VarCond = ~ ["loop body must return Cond" @processor block compilerError] when

          processor compilable [
            condition staticityOfVar Weak > [
              appliedVars.curToNested [
                pair:;
                pair.value pair.key copy changeVarValue
              ] each

              newNode newNodeIndex @appliedVars applyStackChanges
              a: @processor @block pop;
              VarCond a getVar.data.get copy
            ] [
              TRUE dynamic @loopIsDynamic set
              FALSE
            ] if
          ] &&
        ] &&

        @appliedVars.@fixedOutputs @processor.releaseVarRefArray
      ] if
    ] &&

    iterationNumber 1 + @iterationNumber set
    iterationNumber processor.options.staticLoopLengthLimit > [
      TRUE @processor.@result.!passErrorThroughPRE
      ("Static loop length limit (" processor.options.staticLoopLengthLimit ") exceeded. Dynamize loop or increase limit using -static_loop_lenght_limit option") assembleString @processor block compilerError
    ] when

    processor compilable and
  ] loop

  loopIsDynamic [indexArray file processDynamicLoop] when
];

processDynamicLoop: [
  indexArray: file:;;

  iterationNumber: 0 dynamic;
  [
    needToRemake: FALSE dynamic;
    newNodeIndex: @indexArray @processor @block tryMatchAllNodes;
    newNodeIndex 0 < [processor compilable] && [
      "dynamicLoop" makeStringView
      block.id
      NodeCaseCode
      indexArray
      file
      positionInfo
      CFunctionSignature
      @processor astNodeToCodeNode @newNodeIndex set
    ] when

    newNodeIndex usePreInputs

    processor compilable [
      newNode: newNodeIndex @processor.@blocks.at.get;
      newNodeIndex changeNewNodeState

      newNode.state NodeStateHasOutput < [
        FALSE
      ] [
        newNode.state NodeStateHasOutput = [NodeStateHasOutput @block.@state set] when

        appliedVars: newNodeIndex applyNodeChanges;

        checkToRecompile: [
          dst:;
          src:;

          result: FALSE dynamic;
          src dst variablesAreSame [
            src staticityOfVar Weak >
            [src dst processor variablesAreEqual ~] && [
              TRUE @result set
            ] when
          ] [
            "loop body changes stack types" @processor block compilerError
          ] if

          result
        ];

        appliedVars.curToNested [
          pair:;

          pair.key pair.value checkToRecompile [
            pair.value staticityOfVar Dirty = [
              pair.key copy @processor @block makeVarDirty
            ] [
              pair.key copy @processor @block makeVarDynamic
            ] if
            pair.key copy @processor @block makePointeeDirtyIfRef
            TRUE dynamic @needToRemake set
          ] when
        ] each

        newNode.outputs.dataSize newNode.matchingInfo.inputs.dataSize 1 + = ~ ["loop body must save stack values and return Cond" @processor block compilerError] when
        processor compilable [
          condition: newNode.outputs.last.refToVar;
          condVar: condition getVar;
          condVar.data.getTag VarCond = ~ ["loop body must return Cond" @processor block compilerError] when

          i: 0 dynamic;
          [
            i newNode.matchingInfo.inputs.dataSize < [
              curInput: i @processor block getStackEntry;
              curOutput: newNode.matchingInfo.inputs.dataSize 1 - i - newNode.outputs.at .refToVar;
              curInput curOutput checkToRecompile [
                curInput @processor @block makeVarTreeDynamic
                TRUE dynamic @needToRemake set
              ] when
              i 1 + @i set TRUE
            ] &&
          ] loop
        ] when

        needToRemake ~ processor compilable and [
          inputs:     @processor.acquireVarRefArray;
          nodeInputs: @processor.acquireVarRefArray;
          outputs:    @processor.acquireVarRefArray;

          # apply stack changes
          i: 0 dynamic;
          [
            i newNode.matchingInfo.inputs.dataSize < [
              @processor @block pop @inputs.pushBack
              i 1 + @i set TRUE
            ] &&
          ] loop

          i: 0 dynamic;
          [
            i appliedVars.fixedOutputs.getSize < [
              curOutput: i appliedVars.fixedOutputs.at;
              curOutput @outputs.pushBack
              curOutput getVar.data.getTag VarStruct = [
                curOutput @block.@candidatesToDie.pushBack
              ] when

              i 1 + newNode.outputs.dataSize < [
                curOutput @block push
              ] when
              i 1 + @i set TRUE
            ] &&
          ] loop

          createPhiNodes: [
            i: 0 dynamic;
            [
              i inputs.getSize < [
                curNodeInput: i inputs.at @processor @block copyVar;
                curNodeInput @nodeInputs.pushBack

                (curNodeInput @processor getIrType "*") assembleString makeStringView # with *
                curNodeInput @processor getIrName
                i inputs.at @processor getIrName
                inputs.dataSize 1 - i - outputs.at @processor getIrName
                1 @block createPhiNode

                i 1 + @i set TRUE
              ] &&
            ] loop
          ];

          # create instruction
          processor.options.verboseIR ["loop prepare..." @block createComment] when
          1 @block createJump
          @block createLabel
          createPhiNodes # for each input-output!
          processor.options.verboseIR ["phi nodes prepared" @block createComment] when
          nodeInputs @outputs newNode makeCallInstruction

          implicitDerefInfo: @processor.@condArray;
          newNode.outputs [.argCase isImplicitDeref @implicitDerefInfo.pushBack] each
          implicitDerefInfo outputs.getSize 1 - @block derefNEntries
          processor.options.verboseIR ["loop end prepare..." @block createComment] when
          1 outputs.last @processor @block createBranch
          @block createLabel

          @inputs     @processor.releaseVarRefArray
          @nodeInputs @processor.releaseVarRefArray
          @outputs    @processor.releaseVarRefArray

          @implicitDerefInfo.clear
        ] when

        needToRemake [
          newNodeIndex processor.blocks.at.get.nodeCompileOnce [
            "loop body compileOnce directive fail" @processor block compilerError
          ] when

          newNodeIndex @processor deleteNode

          iterationNumber processor.options.staticLoopLengthLimit > [
            "loop dynamisation iteration count so big" @processor block compilerError
          ] when
        ] when

        iterationNumber 1 + @iterationNumber set

        needToRemake processor compilable and

        @appliedVars.@fixedOutputs @processor.releaseVarRefArray
      ] if
    ] &&
  ] loop
];

{
  block: Block Ref; processor: Processor Ref;
  asCodeRef: Cond; name: StringView Cref; signature: CFunctionSignature Cref;} Natx {} [
  block:;
  processor:;
  overload failProc: @processor block FailProcForProcessor;

  copy asCodeRef:;
  name:;
  signature:;
  compileOnce

  @processor addBlock
  declarationNode: @processor.@blocks.last.get;
  block.id @declarationNode.@parent set
  asCodeRef [NodeCaseCodeRefDeclaration][NodeCaseDeclaration] if @declarationNode.@nodeCase set
  signature.variadic @declarationNode.@variadic set

  signature.inputs.getSize [
    r: signature.inputs.getSize 1 - i - signature.inputs.at @processor @block copyVarFromChild;
    @r @processor block unglobalize
    FALSE @r.setMutable
    r @block push
  ] times

  [
    compilerPositionInfo: processor.positions.last copy;
    block: @declarationNode;
    forcedSignature: signature;
    processor.options.debug [
      @processor addDebugReserve @block.@funcDbgIndex set
    ] when
    forcedSignature.inputs   [p:; a: @processor @block pop;] each
    forcedSignature.outputs [@processor @block copyVarFromChild @block push] each
    name compilerPositionInfo forcedSignature @processor @block finalizeCodeNode
  ] call

  signature.inputs   [p:; a: @processor @block pop;] each
  declarationNode storageAddress
] "processImportFunction" exportFunction

{block: Block Ref; processor: Processor Ref; 
  asLambda: Cond; name: StringView Cref; file: File Cref; astNode: AstNode Cref; signature: CFunctionSignature Cref;} Int32 {} [
  block:;
  processor:;
  copy asLambda:;
  name:;
  file:;
  astNode:;
  signature:;
  overload failProc: @processor block FailProcForProcessor;

  indexArray: AstNodeType.Code astNode.data.get;
  positionInfo: astNode file makeCompilerPosition;
  compileOnce

  signature.variadic [
    "export function cannot be variadic" @processor block compilerError
  ] when

  ("process export: " makeStringView name makeStringView) addLog

  # we dont know count of used in export entites
  signature.inputs.getSize [
    r: signature.inputs.getSize 1 - i - signature.inputs.at @processor @block copyVarFromChild;
    r @processor @block makeVarTreeDynamic
    @r @processor block unglobalize
    @r fullUntemporize
    r getVar.data.getTag VarRef = [
      @r @processor @block getPointeeNoDerefIR @block push
    ] [
      FALSE @r.setMutable
      r @block push
    ] if
  ] times

  oldSuccess: processor compilable;
  oldRecursiveNodesStackSize: processor.recursiveNodesStack.getSize;

  newNodeIndex: @indexArray @processor @block tryMatchAllNodesForRealFunction;
  newNodeIndex 0 < [processor compilable] && [
    nodeCase: asLambda [NodeCaseLambda][NodeCaseExport] if;
    processor.exportDepth 1 + @processor.@exportDepth set
    name block.id nodeCase indexArray file positionInfo signature @processor astNodeToCodeNode @newNodeIndex set
    processor.exportDepth 1 - @processor.@exportDepth set
  ] when

  newNodeIndex usePreCaptures

  processor compilable [
    newNodeIndex changeNewExportNodeState

    newNode: newNodeIndex processor.blocks.at.get;
    newNode.outputs.getSize 1 > ["export function cant have 2 or more outputs" @processor block compilerError] when
    newNode.outputs.getSize 1 = [signature.outputs.getSize 0 =] && ["signature is void, export function must be without output" @processor block compilerError] when
    newNode.outputs.getSize 0 = [signature.outputs.getSize 1 =] && ["signature is not void, export function must have output" @processor block compilerError] when
    newNode.state NodeStateCompiled = ~ [
      "can not implement lambda inside itself body" @processor block compilerError
      FALSE @oldSuccess set
    ] when

    processor compilable [
      signature.outputs.getSize [
        currentInNode: i newNode.outputs.at.refToVar;
        currentInSignature: i signature.outputs.at;

        currentInNode currentInSignature variablesAreSame ~ [
          ("export function output mismatch, expected " currentInSignature @processor block getMplType ";" LF
            "but found " currentInNode @processor block getMplType) assembleString @processor block compilerError
        ] when
      ] times
    ] when
  ] when

  signature.inputs [p:; a: @processor @block pop;] each

  processor compilable [
    ("successfully processed export: " makeStringView name makeStringView) addLog
  ] [
    ("failed while process export: " makeStringView name makeStringView) addLog
  ] if

  oldSuccess processor compilable ~ and processor.depthOfPre 0 = and processor.result.findModuleFail ~ and [
    @processor.@result.@errorInfo move @processor.@result.@globalErrorInfo.pushBack
    oldRecursiveNodesStackSize @processor.@recursiveNodesStack.shrink
    -1 @processor.@result clearProcessorResult

    signature name FALSE dynamic @processor @block processImportFunction Block addressToReference .id copy !newNodeIndex
  ] when

  newNodeIndex
] "processExportFunction" exportFunction

callImportWith: [
  declarationNode: refToVar: dynamicFunc: block:;;;;
  inputs:  @processor.acquireVarRefArray;
  outputs: @processor.acquireVarRefArray;
  (
    [processor compilable]
    [
      i: 0 dynamic;
      [
        i declarationNode.matchingInfo.inputs.dataSize < [
          (
            [processor compilable]
            [stackEntry: @processor @block pop;]
            [
              input: stackEntry copy;
              @input makeVarRealCaptured
              nodeEntry: i @declarationNode.@matchingInfo.@inputs.at.@refToVar;
              nodeMutable: nodeEntry.mutable;
              i declarationNode.csignature.inputs.at getVar.data.getTag VarRef = [
                TRUE @stackEntry getVar.@capturedAsMutable set
              ] when

              stackEntry nodeEntry variablesAreSame ~ [
                lambdaCastResult: input @nodeEntry @processor @block tryImplicitLambdaCast;
                lambdaCastResult.success [
                  lambdaCastResult.refToVar @input set
                ] [
                  ("cant call import, variable types of argument #" i " are incorrect, expected " nodeEntry @processor block getMplType ";" LF "but found " stackEntry @processor block getMplType) assembleString @processor block compilerError
                ] if
              ] when
            ] [
              stackEntry.mutable ~ nodeMutable and [
                ("cant call import, expected mutable argument #" i " with type " nodeEntry @processor block getMplType) assembleString @processor block compilerError
              ] when
            ] [
              nodeMutable [stackEntry @processor @block makeVarTreeDirty] when
              input @inputs.pushBack
            ]
          ) sequence
          i 1 + @i set processor compilable
        ] &&
      ] loop
    ] [
      declarationNode.variadic [
        (
          [processor compilable]
          [refToVarargs: @processor @block pop;]
          [
            varargs: refToVarargs getVar;
            varargs.data.getTag VarStruct = ~ ["varargs must be a struct" @processor block compilerError] when
          ] [
            varStruct: VarStruct varargs.data.get.get;
            varStruct.fields.getSize [
              field: i @refToVarargs @processor @block processStaticAt;
              field @inputs.pushBack
            ] times
          ]
        ) sequence
      ] when
    ] [
      i: 0 dynamic;
      [
        i declarationNode.outputs.getSize < [
          currentOutput: i declarationNode.outputs.at.refToVar;
          current: currentOutput @processor @block copyVarFromChild;
          Dynamic @current getVar.@staticity set
          current @outputs.pushBack
          current getVar.data.getTag VarStruct = [
            current @block.@candidatesToDie.pushBack
          ] when

          i 1 + @i set processor compilable
        ] &&
      ] loop
    ] [
      forcedName: StringView;
      inputs @outputs declarationNode forcedName refToVar dynamicFunc @block makeCallInstructionWith
      i: 0 dynamic;
      [
        i outputs.getSize < [
          currentOutput: i outputs.at;
          currentOutput @block push
          i 1 + @i set processor compilable
        ] &&
      ] loop
    ] [
      implicitDerefInfo: @processor.@condArray;
      outputs [
        getVar.data.getTag VarRef = @implicitDerefInfo.pushBack
      ] each

      implicitDerefInfo outputs.getSize @block derefNEntries
      @implicitDerefInfo.clear
    ]
  ) sequence

  @inputs  @processor.releaseVarRefArray
  @outputs @processor.releaseVarRefArray
];

{block: Block Ref; processor: Processor Ref;
  refToVar: RefToVar Cref;} () {} [
  block:;
  processor:;
  overload failProc: @processor block FailProcForProcessor;

  refToVar:;
  var: refToVar getVar;
  protoIndex: VarImport var.data.get copy;
  node: protoIndex @processor.@blocks.at.get;
  [
    node.nextRecLambdaId 0 < ~ [
      node.nextRecLambdaId @protoIndex set
      protoIndex @processor.@blocks.at.get !node
      TRUE
    ] &&
  ] loop

  dynamicFunc: refToVar staticityOfVar Dynamic > ~;
  dynamicFunc ~ [
    node.nodeCase NodeCaseCodeRefDeclaration = [
      "nullpointer call" @processor block compilerError
    ] when
  ] when

  @node refToVar dynamicFunc @block callImportWith
] "processFuncPtr" exportFunction
