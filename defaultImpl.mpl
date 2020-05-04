"control" use

"conventions.cdecl" use

"String.addLog" use
"String.assembleString" use
"String.print" use
"String.printList" use
"String.toString" use
"String.StringView" use
"String.makeStringView" use

"declarations.defaultPrintStack" use
"declarations.defaultPrintStackTrace" use
"declarations.compilerError" use
"declarations.createRefWith" use
"declarations.createCopyToExists" use
"declarations.getMplType" use
"declarations.popWith" use
"declarations.processCall" use
"declarations.processFuncPtr" use
"declarations.push" use
"declarations.tryImplicitLambdaCast" use
"Block.Block" use
"Block.NodeStateNew" use
"Block.NodeCaseCodeRefDeclaration" use
"processor.Processor" use
"Var.getVar" use
"Var.RefToVar" use
"Var.variablesAreSame" use
"Var.VarCode" use
"Var.VarImport" use
"Var.VarString" use
"Var.Weak" use
"Var.staticityOfVar" use

FailProcForProcessor: [{
  processor: block: ;;

  CALL: [
    overload failProc: [print " - fail while handling fail" print];
    print

    trace: getCallTrace;
    [
      trace.first trace.last is [
        FALSE
      ] [
        () "\nin \00" printf
        trace.last.name print
        (trace.last.line copy trace.last.column copy) " at %i:%i\00" printf
        trace.last.prev trace.last addressToReference @trace.!last
        TRUE
      ] if
    ] loop

    "\nWhile compiling:\n" print
    @processor block defaultPrintStackTrace

    2 exit
  ];
} dynamic];

pop: [
  processor: block: ;;
  result: RefToVar;
  @result FALSE @processor @block popWith
  @result
];

createRef:     [processor: block:;;  TRUE dynamic @processor @block createRefWith];
createRefNoOp: [processor: block:;; FALSE dynamic @processor @block createRefWith];

compilable: [processor:; processor.result.success copy];

makeVarRealCaptured: [
  refToVar:;
  TRUE @refToVar getVar.@capturedAsRealValue set
];

defaultFailProc: [
  processor: block: ;;
  text: @processor @block pop;
];

defaultSet: [
  processor: block: ;;
  refToDst: @processor @block pop;
  refToSrc: @processor @block pop;
  processor compilable [
    @refToSrc makeVarRealCaptured
    @refToDst makeVarRealCaptured

    refToDst refToSrc variablesAreSame [
      refToSrc getVar.data.getTag VarImport = [
        "functions cannot be copied" @processor block compilerError
      ] [
        refToSrc getVar.data.getTag VarString = [
          "builtin-strings cannot be copied" @processor block compilerError
        ] [
          refToDst.mutable [
            [refToDst staticityOfVar Weak = ~] "Destination is weak!" assert
            @refToSrc refToDst @processor @block createCopyToExists
          ] [
            "destination is immutable" @processor block compilerError
          ] if
        ] if
      ] if
    ] [
      refToDst.mutable ~ [
        "destination is immutable" @processor block compilerError
      ] [
        lambdaCastResult: refToSrc @refToDst @processor @block tryImplicitLambdaCast;
        lambdaCastResult.success [
          newSrc: @lambdaCastResult.@refToVar TRUE @processor @block createRef;
          @newSrc refToDst @processor @block createCopyToExists
        ] [
          ("types mismatch, src is " refToSrc @processor block getMplType "," LF "dst is " refToDst @processor block getMplType) assembleString @processor block compilerError
        ] if
      ] if
    ] if
  ] when
];

defaultRef: [
  mutable: processor: block: ;;;
  refToVar: @processor @block pop;
  processor compilable [
    @refToVar mutable @processor @block createRef @block push
  ] when
];

defaultMakeConstWith: [
  check: processor: block: ;;;
  refToVar: @processor @block pop;
  processor compilable [
    check [refToVar getVar.temporary copy] && [
      "temporary objects cannot be set const" @processor block compilerError
    ] [
      FALSE @refToVar.setMutable
      refToVar @block push
    ] if
  ] when
];
getStackEntryWith: [
  depth: check: block: ;; copy;
  result: RefToVar @block isConst [Cref] [Ref] uif; #ref to 0nx
  currentBlock: @block; [
    currentBlock.root [
      check ["stack underflow" @processor block compilerError] when
      FALSE
    ] [
      depth currentBlock.stack.dataSize < [
        currentBlock.stack.dataSize 1 - depth - @currentBlock.@stack.at !result
        FALSE
      ] [
        depth currentBlock.stack.dataSize - currentBlock.buildingMatchingInfo.inputs.dataSize + @depth set
        currentBlock.parent @processor.@blocks.at.get !currentBlock
        TRUE
      ] if
    ] if
  ] loop

  @result
];

getStackEntry:          [depth: processor: block:;; copy; depth TRUE  @block getStackEntryWith];
getStackEntryUnchecked: [depth: processor: block:;; copy; depth FALSE block  getStackEntryWith];

getStackDepth: [
  processor: block:;;
  depth: 0 dynamic;
  inputsCount: 0 dynamic;
  [
    block.root ~ [
      depth block.stack.dataSize + @depth set
      inputsCount block.buildingMatchingInfo.inputs.dataSize + @inputsCount set
      block.parent processor.blocks.at.get !block
      TRUE
    ] &&
  ] loop

  [inputsCount depth > ~] "Missed stack overflow!" assert

  depth inputsCount -
];

{
  block: Block Cref;
  processor: Processor Ref;
} () {} [
  processor: block:;;

  ("stack:" LF "depth=" @processor block getStackDepth LF) printList

  i: 0 dynamic;
  [
    i @processor block getStackDepth < [
      entry: i @processor block getStackEntryUnchecked;
      (entry @processor block getMplType entry.mutable ["R"] ["C"] if entry getVar.temporary ["T"] [""] if LF) printList
      i 1 + @i set TRUE
    ] &&
  ] loop
] "defaultPrintStack" exportFunction

{
  block: Block Cref;
  processor: Processor Ref;
} () {} [
  processor: block: ;;

  processor.positions.getSize [
    currentPosition: processor.positions.getSize 1 - i - processor.positions.at;

    (
      "at filename: " currentPosition.file.name
      ", token: "     currentPosition.token
      ", line: "      currentPosition.line
      ", column: "    currentPosition.column LF
    ) printList
  ] times

  @processor block defaultPrintStack
] "defaultPrintStackTrace" exportFunction

findNameInfo: [
  processor:;
  @processor.@nameManager.createName
];

addStackUnderflowInfo: [
  block:;
  TRUE @block.@buildingMatchingInfo.@hasStackUnderflow set
  block.state NodeStateNew = [
    TRUE @block.@matchingInfo.@hasStackUnderflow set
  ] when
];

nodeHasCode: [
  node:;
  node.emptyDeclaration ~ [node.uncompilable ~] && [node.empty ~] && [node.deleted ~] && [node.nodeCase NodeCaseCodeRefDeclaration = ~] &&
];
