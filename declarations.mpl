"control" use

"String.String" use
"String.StringView" use
"String.makeStringView" use

"astNodeType.AstNode" use
"astNodeType.IndexArray" use
"Block.Block" use
"Block.CFunctionSignature" use
"Block.CompilerPositionInfo" use
"Block.NodeCaseCode" use
"File.File" use
"processor.Processor" use
"processor.RefToVarTable" use
"Var.Variable" use
"Var.RefToVar" use

{
  processor: Processor Ref;
  block: Block Cref;
  message: StringView Cref;
} () {} "compilerErrorImpl" importFunction

compilerError: [processor: block:;; makeStringView block @processor compilerErrorImpl];

{
  processor: Processor Ref;

  signature: CFunctionSignature Cref;
  compilerPositionInfo: CompilerPositionInfo Cref;
  file: File Cref;
  indexArray: IndexArray Cref;
  nodeCase: NodeCaseCode;
  parentIndex: 0;
  functionName: StringView Cref;
} 0 {} "astNodeToCodeNode" importFunction

{
  processor: Processor Ref;

  signature: CFunctionSignature Cref;
  compilerPositionInfo: CompilerPositionInfo Cref;
  refToVar: RefToVar Cref;
} () {} "createDtorForGlobalVar" importFunction

{
  block: Block Ref;
  processor: Processor Ref;

  positionInfo: CompilerPositionInfo Cref;
  name: StringView Cref;
  nodeCase: NodeCaseCode;
  indexArray: IndexArray Cref;
} () {} "processCallByIndexArray" importFunction

{
  block: Block Ref;
  processor: Processor Ref;

  index: Int32;
} () {} "callBuiltin" importFunction

{
  block: Block Ref;
  processor: Processor Ref;

  refToVar: RefToVar Cref;
} () {} "processFuncPtr" importFunction

{
  block: Block Ref;
  processor: Processor Ref;

  file: File Cref;
  preAstNodeIndex: Int32;
} Cond {} "processPre" importFunction

{
  block: Block Ref;
  processor: Processor Ref;

  name: StringView Cref;
  file: File Cref;
  callAstNodeIndex: Int32;
} () {} "processCall" importFunction

{
  block: Block Ref;
  processor: Processor Ref;

  asLambda: Cond;
  name: StringView Cref;
  file: File Cref;
  astNode: AstNode Cref;
  signature: CFunctionSignature Cref;
} Int32 {} "processExportFunction" importFunction

{
  block: Block Ref;
  processor: Processor Ref;

  asCodeRef: Cond;
  name: StringView Cref;
  signature: CFunctionSignature Cref;
} Natx {} "processImportFunction" importFunction

{
  block: Block Cref;
  processor: Processor Ref;

  comparingMessage: String Ref;
  curToNested: RefToVarTable Ref;
  nestedToCur: RefToVarTable Ref;
  currentMatchingNode: Block Cref;
  cacheEntry: RefToVar Cref;
  stackEntry: RefToVar Cref;
} Cond {} "compareEntriesRec" importFunction

{
  block: Block Cref;
  processor: Processor Ref;

  refToVar: RefToVar Cref;
} () {} "makeVariableType" importFunction

{
  block: Block Ref;
  processor: Processor Ref;

  forMatching: Cond;
  result: RefToVar Ref;
} () {} "popWith" importFunction

{
  block: Block Ref;
  entry: RefToVar Cref;
} () {} "push" importFunction

{
  block: Block Ref;
  processor: Processor Ref;

  dynamicStoraged: Cond;
  reason: Nat8;
  end: RefToVar Ref;
  begin: RefToVar Ref;
  refToVar: RefToVar Cref;
} () {} "makeShadowsWith" importFunction

makeShadows: [
  processor: block:;;
  FALSE @processor @block  makeShadowsWith
];

makeShadowsDynamic: [
  processor: block:;;
  TRUE @processor @block makeShadowsWith
];

{
  block: Block Cref;
  processor: Processor Ref;

  refToVar: RefToVar Cref;
} Int32 {} "generateDebugTypeId" importFunction

{
  block: Block Cref;
  processor: Processor Ref;

  refToVar: RefToVar Cref;
} Int32 {} "generateIrTypeId" importFunction

{
  block: Block Cref;
  processor: Processor Ref;

  resultMPL: String Ref;
  refToVar: RefToVar Cref;
} () {}  "getMplTypeImpl" importFunction

getMplType: [
  processor: block: ;;
  result: String;
  @result @processor block getMplTypeImpl
  @result
];

{
  block: Block Cref;
  processor: Processor Ref;
} () {} "defaultPrintStack" importFunction

{
  block: Block Cref;
  processor: Processor Ref;
} () {} "defaultPrintStackTrace" importFunction

{
  block: Block Ref;
  processor: Processor Ref;
  createOperation: Cond;
  mutable: Cond;
  refToVar: RefToVar Cref;
  result: RefToVar Ref;
} () {} "createRefWithImpl" importFunction

createRefWith: [
  refToVar: mutable: createOperation: processor: block: ;;;;;
  result: RefToVar;

  @result refToVar mutable createOperation @processor @block createRefWithImpl
  @result
];

{
  block: Block Ref;
  processor: Processor Ref;
  refToVar: RefToVar Cref;
} () {} "callInit" importFunction

{
  block: Block Ref;
  processor: Processor Ref;
  refToDst: RefToVar Cref;
  refToSrc: RefToVar Cref;
} () {} "callAssign" importFunction

{
  block: Block Ref;
  processor: Processor Ref;
  refToVar: RefToVar Cref;
} () {} "callDie" importFunction

{
  block: Block Ref;
  processor: Processor Ref;
  refToDst: RefToVar Cref;
  refToSrc: RefToVar Cref;
} () {} "setVar" importFunction

TryImplicitLambdaCastResult: [{
  success: FALSE dynamic;
  refToVar: RefToVar;
}];

{
  block: Block Ref;
  processor: Processor Ref;
  refToDst: RefToVar Cref;
  refToSrc: RefToVar Cref;
  result: TryImplicitLambdaCastResult Ref;
} () {} "tryImplicitLambdaCastImpl" importFunction

tryImplicitLambdaCast: [
  refToSrc: refToDst: processor: block: ;;;;
  result: TryImplicitLambdaCastResult;

  @result refToSrc refToDst @processor @block tryImplicitLambdaCastImpl
  @result
];


{
  block: Block Ref;
  processor: Processor Ref;

  toNew: Cond;
  fromChildToParent: Cond;
  refToVar: RefToVar Cref;
  result: RefToVar Ref;
} () {} "copyVarImpl" importFunction

copyVarWith: [
  refToVar: fromChildToParent: toNew: processor: block: ;;;;;

  result: RefToVar;
  @result refToVar fromChildToParent toNew @processor @block copyVarImpl
  @result
];

copyVar:           [processor: block:;; FALSE dynamic FALSE dynamic @processor @block copyVarWith]; #fromchild is static arg
copyVarFromChild:  [processor: block:;; TRUE  dynamic FALSE dynamic @processor @block copyVarWith];
copyVarToNew:      [processor: block:;; FALSE dynamic TRUE  dynamic @processor @block copyVarWith];
copyVarFromParent: [processor: block:;; TRUE  dynamic FALSE dynamic @processor @block copyVarWith];
