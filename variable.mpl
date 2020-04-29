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
"String.splitString" use
"String.toString" use
"conventions.cdecl" use

"Block.Block" use
"Block.CFunctionSignature" use
"Block.CompilerPositionInfo" use
"Block.NameCaseInvalid" use
"Block.NodeCaseCode" use
"File.File" use
"Var.getStringImplementation" use
"Var.getSingleDataStorageSize" use
"Var.getStorageSize" use
"Var.getVar" use
"Var.getVirtualValue" use
"Var.isAutoStruct" use
"Var.isNonrecursiveType" use
"Var.isStruct" use
"Var.isSingle" use
"Var.isPlain" use
"Var.isVirtual" use
"Var.isVirtualType" use
"Var.makeStringId" use
"Var.RefToVar" use
"Var.Schema" use
"Var.VarBuiltin" use
"Var.VarCode" use
"Var.VarCond" use
"Var.VarImport" use
"Var.VarInt8" use
"Var.VarInt16" use
"Var.VarInt32" use
"Var.VarInt64" use
"Var.VarIntX" use
"Var.VarNat8" use
"Var.VarNat16" use
"Var.VarNat32" use
"Var.VarNat64" use
"Var.VarNatX" use
"Var.VarReal32" use
"Var.VarReal64" use
"Var.VarRef" use
"Var.VarString" use
"Var.VarStruct" use
"Var.Variable" use
"Var.Virtual" use
"astNodeType.AstNode" use
"astNodeType.IndexArray" use
"defaultImpl.failProcForProcessor" use
"debugWriter.getTypeDebugDeclaration" use
"irWriter.compilerError" use
"irWriter.createTypeDeclaration" use
"irWriter.getIrType" use
"irWriter.getMplSchema" use
"irWriter.getNameById" use
"irWriter.generateRegisterIRName" use
"irWriter.generateVariableIRNameWith" use
"processor.Processor" use
"processor.ProcessorResult" use
"processor.RefToVarTable" use
"schemas.getVariableSchemaId" use
"schemas.makeVariableSchema" use

Overload: [NameInfoEntry Array];

makeNameInfo: [{
  name: copy;
  stack: Overload Array;
}];

NameInfo: [String makeNameInfo];

compilable: [processor:; processor.result.success copy];

callBuiltin:           [block:; @block @processor callBuiltinImpl];
processFuncPtr:        [@block @processor processFuncPtrImpl];

processPre: [
  preAstNodeIndex: file:;;
  preAstNodeIndex file @block @processor processPreImpl
];

processCall: [
  callAstNodeIndex: file: name:;;;
  callAstNodeIndex file name @block @processor processCallImpl
];

processExportFunction: [
  signature: astNode: file: name: asLambda: block:;;;;;;
  signature astNode file name asLambda @block @processor processExportFunctionImpl
];

processImportFunction: [@block @processor processImportFunctionImpl];
compareEntriesRec:     [currentMatchingNode @nestedToCur @curToNested @comparingMessage block @processor compareEntriesRecImpl];
makeVariableType:      [processor: block:;; block @processor makeVariableTypeImpl];
generateDebugTypeId:   [processor: block:;; block @processor generateDebugTypeIdImpl];
generateIrTypeId:      [processor: block:;; block @processor generateIrTypeIdImpl];

getMplType: [
  processor: block: ;;
  result: String;
  @result block @processor getMplTypeImpl
  @result
];

{
  signature: CFunctionSignature Cref;
  compilerPositionInfo: CompilerPositionInfo Cref;
  file: File Cref;
  indexArray: IndexArray Cref;
  processor: Processor Ref;
  nodeCase: NodeCaseCode;
  parentIndex: 0;
  functionName: StringView Cref;
} 0 {convention: cdecl;} "astNodeToCodeNode" importFunction

{
  signature: CFunctionSignature Cref;
  compilerPositionInfo: CompilerPositionInfo Cref;
  processor: Processor Ref;
  refToVar: RefToVar Cref;
} () {convention: cdecl;} "createDtorForGlobalVar" importFunction

{
  processor: Processor Ref;
  block: Block Ref;
  positionInfo: CompilerPositionInfo Cref;
  name: StringView Cref;
  nodeCase: NodeCaseCode;
  indexArray: IndexArray Cref;
} () {convention: cdecl;} "processCallByIndexArrayImpl" importFunction

{
  processor: Processor Ref;
  block: Block Ref;
  index: Int32;
} () {convention: cdecl;} "callBuiltinImpl" importFunction

{
  processor: Processor Ref;
  block: Block Ref;
  refToVar: RefToVar Cref;
} () {convention: cdecl;} "processFuncPtrImpl" importFunction

{
  processor: Processor Ref;
  block: Block Ref;
  file: File Cref;
  preAstNodeIndex: Int32;
} Cond {convention: cdecl;} "processPreImpl" importFunction

{
  processor: Processor Ref;
  block: Block Ref;
  name: StringView Cref;
  file: File Cref;
  callAstNodeIndex: Int32;
} () {convention: cdecl;} "processCallImpl" importFunction

{
  processor: Processor Ref;
  block: Block Ref;
  asLambda: Cond;
  name: StringView Cref;
  file: File Cref;
  astNode: AstNode Cref;
  signature: CFunctionSignature Cref;
} Int32 {convention: cdecl;} "processExportFunctionImpl" importFunction

{
  processor: Processor Ref;
  block: Block Ref;
  asCodeRef: Cond;
  name: StringView Cref;
  signature: CFunctionSignature Cref;
} Natx {convention: cdecl;} "processImportFunctionImpl" importFunction

{
  processor: Processor Ref;
  block: Block Cref;

  comparingMessage: String Ref;
  curToNested: RefToVarTable Ref;
  nestedToCur: RefToVarTable Ref;
  currentMatchingNode: Block Cref;
  cacheEntry: RefToVar Cref;
  stackEntry: RefToVar Cref;
} Cond {convention: cdecl;} "compareEntriesRecImpl" importFunction

{
  processor: Processor Ref;
  block: Block Cref;
  refToVar: RefToVar Cref;
} () {convention: cdecl;} "makeVariableTypeImpl" importFunction

{
  forMatching: Cond;
  processor: Processor Ref;
  block: Block Ref;
  result: RefToVar Ref;
} () {convention: cdecl;} "popImpl" importFunction

{
  dynamicStoraged: Cond;

  processor: Processor Ref;
  block: Block Ref;

  reason: Nat8;
  end: RefToVar Ref;
  begin: RefToVar Ref;
  refToVar: RefToVar Cref;
} () {convention: cdecl;} "makeShadowsImpl" importFunction

{
  processor: Processor Ref;
  block: Block Cref;
  refToVar: RefToVar Cref;
} Int32 {} "generateDebugTypeIdImpl" importFunction

{
  processor: Processor Ref;
  block: Block Cref;
  refToVar: RefToVar Cref;
} Int32 {} "generateIrTypeIdImpl" importFunction

{
  processor: Processor Ref;
  block: Block Cref;
  resultMPL: String Ref;
  refToVar: RefToVar Cref;
} () {}  "getMplTypeImpl" importFunction

getMplName:  [getVar.mplNameId processor.nameManager.getText];

getDbgType:  [@processor getMplSchema.dbgTypeId processor getNameById];
getMplTypeId: [@processor getMplType makeStringId];

getDebugType: [
  refToVar: processor: block:;;;
  dbgType: refToVar getDbgType;
  splitted: dbgType splitString;
  splitted.success [
    splitted.chars.getSize 1024 > [
      1024 @splitted.@chars.shrink
      "..." makeStringView @splitted.@chars.pushBack
    ] when
  ] [
    ("Wrong dbgType name encoding" splitted.chars assembleString) assembleString @processor block compilerError
  ] if

  result: (dbgType hash ".") assembleString;
  splitted.chars @result.catMany
  @result
];

staticityOfVar: [
  refToVar:;
  var: refToVar getVar;
  var.staticity copy
];

maxStaticity: [
  copy s1:;
  copy s2:;
  s1 s2 > [s1 copy][s2 copy] if
];

refsAreEqual: [
  refToVar1:;
  refToVar2:;
  refToVar1.var refToVar2.var is
];

variablesAreSame: [
  refToVar1:;
  refToVar2:;
  refToVar1 getVar.mplSchemaId refToVar2 getVar.mplSchemaId = # id compare better than string compare!
];

markAsAbleToDie: [
  refToVar:;
  var: @refToVar getVar;
  var.data.getTag VarStruct = [FALSE VarStruct @var.@data.get.get.@unableToDie set] when
];

isStaticData: [
  refToVar:;
  var: refToVar getVar;
  refToVar isVirtual ~ [var.data.getTag VarStruct =] && [
    unfinished: RefToVar Array;
    refToVar @unfinished.pushBack
    result: TRUE dynamic;
    [
      result [unfinished.getSize 0 >] && [
        current: unfinished.last copy;
        @unfinished.popBack
        current isVirtual [
        ] [
          current isPlain [
            current staticityOfVar Weak < [
              FALSE dynamic @result set
            ] when
          ] [
            curVar: current getVar;
            curVar.data.getTag VarStruct = [
              struct: VarStruct curVar.data.get.get;
              struct.fields [.refToVar @unfinished.pushBack] each
            ] [
              FALSE dynamic @result set
            ] if
          ] if
        ] if
        TRUE
      ] &&
    ] loop
    result
  ] [
    FALSE
  ] if
];

getPlainDataIRType: [
  var: getVar;
  result: String;
  var.data.getTag (
    VarCond  ["i1" toString @result set]
    VarInt8  ["i8" toString @result set]
    VarInt16 ["i16" toString @result set]
    VarInt32 ["i32" toString @result set]
    VarInt64 ["i64" toString @result set]
    VarIntX  [
      processor.options.pointerSize 64nx = [
        "i64" toString @result set
      ] [
        "i32" toString @result set
      ] if
    ]
    VarNat8  ["i8" toString @result set]
    VarNat16 ["i16" toString @result set]
    VarNat32 ["i32" toString @result set]
    VarNat64 ["i64" toString @result set]
    VarNatX  [
      processor.options.pointerSize 64nx = [
        "i64" toString @result set
      ] [
        "i32" toString @result set
      ] if
    ]
    VarReal32 ["float" toString @result set]
    VarReal64 ["double" toString @result set]
    [
      ("Tag = " var.data.getTag) addLog
      [FALSE] "Unknown plain struct while getting IR type" assert
    ]
  ) case

  @result
];

getPlainDataMPLType: [
  compileOnce
  var: getVar;
  result: String;
  var.data.getTag (
    VarCond   ["i1" toString @result set]
    VarInt8   ["i8" toString @result set]
    VarInt16  ["i16" toString @result set]
    VarInt32  ["i32" toString @result set]
    VarInt64  ["i64" toString @result set]
    VarIntX   ["ix" toString @result set]
    VarNat8   ["n8" toString @result set]
    VarNat16  ["n16" toString @result set]
    VarNat32  ["n32" toString @result set]
    VarNat64  ["n64" toString @result set]
    VarNatX   ["nx" toString @result set]
    VarReal32 ["r32" toString @result set]
    VarReal64 ["r64" toString @result set]
    [
      ("Tag = " var.data.getTag) addLog
      [FALSE] "Unknown plain struct MPL type" assert
    ]
  ) case

  @result
];

getNonrecursiveDataIRType: [
  refToVar: block:;;
  refToVar isPlain [
    refToVar getPlainDataIRType
  ] [
    result: String;
    var: refToVar getVar;
    var.data.getTag VarString = [
      "i8" toString @result set
    ] [
      var.data.getTag VarImport = [
        VarImport var.data.get getFuncIrType toString @result set
      ] [
        var.data.getTag VarCode = [var.data.getTag VarBuiltin =] ||  [
          "ERROR" toString @result set
        ] [
          "Unknown nonrecursive struct" @processor block compilerError
        ] if
      ] if
    ] if

    @result
  ] if
];

getNonrecursiveDataMPLType: [
  refToVar: block:;;
  refToVar isPlain [
    refToVar getPlainDataMPLType
  ] [
    result: String;
    var: refToVar getVar;
    var.data.getTag VarString = [
      "s" toString @result set
    ] [
      var.data.getTag VarCode = [
        "c" toString @result set
      ] [
        var.data.getTag VarBuiltin = [
          "b" toString @result set
        ] [
          var.data.getTag VarImport = [
            ("F" VarImport var.data.get block getFuncMplType) assembleString @result set
          ] [
            "Unknown nonrecursive struct" @processor block compilerError
          ] if
        ] if
      ] if
    ] if

    @result
  ] if
];

getNonrecursiveDataDBGType: [
  refToVar: block:;;
  refToVar isPlain [
    refToVar getPlainDataMPLType
  ] [
    result: String;
    var: refToVar getVar;
    var.data.getTag VarString = [
      "s" toString @result set
    ] [
      var.data.getTag VarCode = [
        "c" toString @result set
      ] [
        var.data.getTag VarBuiltin = [
          "b" toString @result set
        ] [
          var.data.getTag VarImport = [
            ("F" VarImport var.data.get getFuncDbgType) assembleString @result set
          ] [
            "Unknown nonrecursive struct" @processor block compilerError
          ] if
        ] if
      ] if
    ] if

    @result
  ] if
];

getStructStorageSize: [
  refToVar: processor: ;;
  var: refToVar getVar;
  struct: VarStruct var.data.get.get;
  struct.structStorageSize copy
];

makeStructStorageSize: [
  refToVar: processor: block: ;;;
  result: 0nx;
  var: @refToVar getVar;
  struct: VarStruct @var.@data.get.get;
  maxA: 1nx;
  j: 0;
  [
    j struct.fields.dataSize < [
      curField: j struct.fields.at;
      curField.refToVar isVirtual ~ [
        curS: curField.refToVar @processor block getStorageSize;
        curA: curField.refToVar @processor block getAlignment;
        result curA + 1nx - curA 1nx - ~ and curS + @result set
        curA maxA > [curA @maxA set] when
      ] when

      j 1 + @j set TRUE
    ] &&
  ] loop

  result maxA + 1nx - maxA 1nx - ~ and @result set
  result @struct.@structStorageSize set
];

getStructAlignment: [
  refToVar:;
  var: refToVar getVar;
  struct: VarStruct var.data.get.get;
  struct.structAlignment copy
];

makeStructAlignment: [
  refToVar: processor: block: ;;;
  result: 0nx;
  var: @refToVar getVar;
  struct: VarStruct @var.@data.get.get;
  j: 0;
  [
    j struct.fields.dataSize < [
      curField: j struct.fields.at;
      curField.refToVar isVirtual ~ [
        curA: curField.refToVar @processor block getAlignment;
        result curA < [curA @result set] when
      ] when
      j 1 + @j set TRUE
    ] &&
  ] loop

  result @struct.@structAlignment set
];

getAlignment: [
  refToVar: processor: block:;;;
  refToVar isSingle [
    refToVar @processor block getSingleDataStorageSize
  ] [
    refToVar getStructAlignment
  ] if
];

isGlobal: [
  refToVar:;
  var: refToVar getVar;
  var.global copy
];

unglobalize: [
  refToVar: processor: block:;;;
  var: @refToVar getVar;
  var.global [
    FALSE @var.@global set
    -1 dynamic @var.@globalId set
    @refToVar @processor block makeVariableIRName
  ] when
];

untemporize: [
  refToVar:;
  var: @refToVar getVar;
  FALSE @var.@temporary set
];

fullUntemporize: [
  refToVar:;
  var: @refToVar getVar;
  FALSE @var.@temporary set
  var.data.getTag VarStruct = [
    FALSE VarStruct @var.@data.get.get.@forgotten set
  ] when
];

noMatterToCopy: [
  refToVar:;
  refToVar isVirtual [refToVar isAutoStruct ~] &&
];

makeTypeAliasId: [
  irTypeName:;

  irTypeName.size 0 > [

    fr: irTypeName makeStringView @processor.@typeNames.find;
    fr.success [
      fr.value copy
    ] [
      newTypeName: ("%type." processor.lastTypeId) assembleString;
      processor.lastTypeId 1 + @processor.@lastTypeId set

      newTypeName irTypeName @processor createTypeDeclaration
      result: @newTypeName @processor makeStringId;
      @irTypeName move result @processor.@typeNames.insert
      result
    ] if
  ] [
    @irTypeName @processor makeStringId
  ] if
];

getFuncIrType: [
  funcIndex:;
  node: funcIndex processor.blocks.at.get;
  resultId: node.signature toString @processor makeStringId;
  resultId processor getNameById
];

getFuncMplType: [
  funcIndex: block:;;
  result: String;
  node: funcIndex processor.blocks.at.get;

  catData: [
    args:;

    "[" @result.cat
    i: 0;
    [
      i args.getSize < [
        current: i args.at;
        current @processor block getMplType @result.cat
        i 1 + args.getSize < [
          "," @result.cat
        ] when
        i 1 + @i set TRUE
      ] &&
    ] loop
    "]" @result.cat
  ];

  "-"                @result.cat
  node.mplConvention @result.cat
  node.csignature.inputs catData
  node.csignature.outputs catData

  @result
];

getFuncDbgType: [
  Index:;
  result: String;
  node: Index processor.blocks.at.get;

  catData: [
    args:;

    "[" @result.cat
    i: 0;
    [
      i args.getSize < [
        current: i args.at;
        current getDbgType                                            @result.cat
        i 1 + args.getSize < [
          ","                                                         @result.cat
        ] when
        i 1 + @i set TRUE
      ] &&
    ] loop
    "]" @result.cat
  ];

  "-"                @result.cat
  node.mplConvention @result.cat
  node.csignature.inputs catData
  node.csignature.outputs catData

  resultId: @result @processor makeStringId;
  resultId @processor getNameById
];

makeDbgTypeId: [
  refToVar: processor: block: ;;;
  refToVar isVirtualType ~ [
    varSchema: refToVar @processor getMplSchema;
    varSchema.dbgTypeDeclarationId -1 = [
      refToVar @processor block getTypeDebugDeclaration @varSchema.@dbgTypeDeclarationId set
    ] when
  ] when
];

{
  processor: Processor Ref;
  block: Block Cref;
  refToVar: RefToVar Ref;
} () {} [
  processor:;
  block:;
  refToVar:;


  #fill info:

  #struct.homogeneous
  #struct.fullVirtual
  #struct.hasPreField
  #struct.hasDestructor
  #struct.realFieldIndexes
  #struct.structAlignment
  #struct.structStorageSize
  #mplSchemaId

  var: @refToVar getVar;
  var.data.getTag VarStruct = [
    branch: VarStruct @var.@data.get.get;
    realFieldCount: 0;

    @branch.@realFieldIndexes.clear
    TRUE @branch.@homogeneous set
    TRUE @branch.@fullVirtual set
    FALSE @branch.@hasPreField set
    FALSE @branch.@hasDestructor set

    i: 0 dynamic;
    branch.fields.dataSize [
      field0: 0 branch.fields.at;
      fieldi: i branch.fields.at;

      fieldi.nameInfo processor.preNameInfo = [
        TRUE @branch.@hasPreField set
      ] when

      fieldi.refToVar isVirtual [
        -1 @branch.@realFieldIndexes.pushBack
      ] [
        FALSE @branch.@fullVirtual set
        realFieldCount @branch.@realFieldIndexes.pushBack
        realFieldCount 1 + @realFieldCount set
      ] if

      field0.refToVar fieldi.refToVar variablesAreSame ~ [
        FALSE @branch.@homogeneous set
      ] when

      fieldi.nameInfo processor.dieNameInfo = [fieldi.refToVar isAutoStruct] || [
        TRUE @branch.@hasDestructor set
      ] when
    ] times

    @refToVar @processor block makeStructAlignment
    @refToVar @processor block makeStructStorageSize
  ] when

  refToVar @processor makeVariableSchema @processor getVariableSchemaId @var.!mplSchemaId
  varSchema: refToVar @processor getMplSchema;
  varSchema.irTypeId -1 = [
    refToVar @processor block generateIrTypeId @varSchema.!irTypeId
  ] when

  processor.options.debug [varSchema.dbgTypeId -1 =] && [
    refToVar @processor block generateDebugTypeId @varSchema.!dbgTypeId
    refToVar @processor block makeDbgTypeId
  ] when
] "makeVariableTypeImpl" exportFunction

{
  processor: Processor Ref;
  block: Block Cref;
  refToVar: RefToVar Cref;
} Int32 {} [
  processor:;
  block:;
  refToVar:;
  var: refToVar getVar;
  resultDBG: String;
  var.data.getTag (
    [drop refToVar isNonrecursiveType] [refToVar block getNonrecursiveDataDBGType @resultDBG set]
    [VarRef =] [
      branch: VarRef var.data.get;
      pointee: branch getVar;
      branch getDbgType @resultDBG.cat
      "*" @resultDBG.cat
    ]
    [VarStruct =] [
      branch: VarStruct @var.@data.get.get;
      branch.fullVirtual ~ [
        "{" @resultDBG.cat
        branch.fields [
          curField:;
          curField.refToVar isVirtual ~ [
            (curField.nameInfo processor.nameManager.getText ":" curField.refToVar getDbgType ";") @resultDBG.catMany
          ] [
            (curField.nameInfo processor.nameManager.getText ".") @resultDBG.catMany
          ] if
        ] each

        "}" @resultDBG.cat
      ] when
    ]
    [[FALSE] "Unknown variable for IR type" assert]
  ) cond

  @resultDBG @processor makeStringId
] "generateDebugTypeIdImpl" exportFunction

{
  processor: Processor Ref;
  block: Block Cref;
  refToVar: RefToVar Cref;
} Int32 {} [
  processor:;
  block:;
  refToVar:;
  var: refToVar getVar;
  resultIR: String;

  var.data.getTag (
    [drop refToVar isNonrecursiveType] [refToVar block getNonrecursiveDataIRType @resultIR set]
    [VarRef =] [
      branch: VarRef var.data.get;
      pointee: branch getVar;

      branch processor getIrType @resultIR.cat
      "*"  @resultIR.cat
    ]
    [VarStruct =] [
      branch: VarStruct @var.@data.get.get;
      branch.fullVirtual ~ [
        branch.homogeneous [
          ("[" branch.fields.dataSize " x " 0 branch.fields.at.refToVar @processor getIrType "]") @resultIR.catMany
        ] [
          "{" @resultIR.cat
          firstGood: TRUE;
          branch.fields [
            field:;
            field.refToVar isVirtual ~ [
              firstGood ~ [
                ", " @resultIR.cat
              ] when

              field.refToVar @processor getIrType @resultIR.cat
              FALSE @firstGood set
            ] when
          ] each

          "}" @resultIR.cat
        ] if
      ] when
    ]
    [[FALSE] "Unknown variable for IR type" assert]
  ) cond

  irTypeId: Int32;
  var.data.getTag VarStruct = [var.data.getTag VarImport =] || [
    @resultIR makeTypeAliasId @irTypeId set
  ] [
    @resultIR @processor makeStringId @irTypeId set
  ] if

  irTypeId
] "generateIrTypeIdImpl" exportFunction

{
  processor: Processor Ref;
  block: Block Cref;
  resultMPL: String Ref;
  refToVar: RefToVar Cref;
} () {} [
  processor:;
  block:;
  resultMPL:;

  refToVar:;
  var: refToVar getVar;

  refToVar isNonrecursiveType [
    refToVar block getNonrecursiveDataMPLType @resultMPL set
  ] [
    var.data.getTag VarRef = [
      branch: VarRef var.data.get;
      pointee: branch getVar;
      branch @processor block getMplType @resultMPL.cat
      branch.mutable [
        "R" @resultMPL.cat
      ] [
        "C" @resultMPL.cat
      ] if
    ] [
      var.data.getTag VarStruct = [
        branch: VarStruct @var.@data.get.get;
        "{" @resultMPL.cat
        i: 0 dynamic;
        [
          i branch.fields.dataSize < [
            curField: i branch.fields.at;
            (
              curField.nameInfo processor.nameManager.getText ":"
              curField.refToVar @processor block getMplType ";") @resultMPL.catMany
            i 1 + @i set TRUE
          ] &&
        ] loop
        "}" @resultMPL.cat
      ] [
        [FALSE] "Unknown variable for IR type" assert
      ] if
    ] if
  ] if

  refToVar isVirtual [
    ir: refToVar getVirtualValue;
    "'" @resultMPL.cat
    ir @resultMPL.cat
  ] when
] "getMplTypeImpl" exportFunction

cutValue: [
  copy tag:;
  copy value:;
  tag (
    VarNat8  [value  0n8 cast 0n64 cast]
    VarNat16 [value 0n16 cast 0n64 cast]
    VarNat32 [value 0n32 cast 0n64 cast]
    VarNatX  [value processor.options.pointerSize 32nx = [0n32 cast 0n64 cast][copy] if]
    VarInt8  [value 0i8 cast 0i64 cast]
    VarInt16 [value 0i16 cast 0i64 cast]
    VarInt32 [value 0i32 cast 0i64 cast]
    VarIntX  [value processor.options.pointerSize 32nx = [0i32 cast 0i64 cast][copy] if]
    [@value copy]
  ) case
];

checkValue: [
  copy tag:;
  copy value:;
  tag (
    VarNat8  [value 0xFFn64 >]
    VarNat16 [value 0xFFFFn64 >]
    VarNat32 [value 0xFFFFFFFFn64 >]
    VarNatX  [processor.options.pointerSize 32nx = [value 0xFFFFFFFFn64 >] &&]
    VarInt8  [value 0x7Fi64 > [value 0x80i64 neg <] ||]
    VarInt16 [value 0x7FFFi64 > [value 0x8000i64 neg <] ||]
    VarInt32 [value 0x7FFFFFFFi64 > [value 0x80000000i64 neg <] ||]
    VarIntX  [processor.options.pointerSize 32nx = [value 0x7FFFFFFFi64 > [value 0x80000000i64 neg <] ||] &&]
    [FALSE]
  ) case ["number constant overflow" @processor block compilerError] when
  @value
];

zeroValue: [
  copy tag:;
  tag VarCond = [FALSE] [
    tag VarInt8 = [0i64] [
      tag VarInt16 = [0i64] [
        tag VarInt32 = [0i64] [
          tag VarInt64 = [0i64] [
            tag VarIntX = [0i64] [
              tag VarNat8 = [0n64] [
                tag VarNat16 = [0n64] [
                  tag VarNat32 = [0n64] [
                    tag VarNat64 = [0n64] [
                      tag VarNatX = [0n64] [
                        tag VarReal32 = [0.0r64] [
                          tag VarReal64 = [0.0r64] [
                            ("Tag = " makeStringView .getTag 0 cast) addLog
                            [FALSE] "Unknown plain struct while getting Zero value" assert
                          ] if
                        ] if
                      ] if
                    ] if
                  ] if
                ] if
              ] if
            ] if
          ] if
        ] if
      ] if
    ] if
  ] if
];

getStaticStructIR: [
  refToVar:;
  result: String;
  unfinishedVars: RefToVar Array;
  unfinishedTerminators: StringView Array;
  refToVar @unfinishedVars.pushBack
  ", " makeStringView @unfinishedTerminators.pushBack
  [
    unfinishedVars.getSize 0 > [
      current: unfinishedVars.last copy;
      @unfinishedVars.popBack

      current isVirtual [
        [FALSE] "Virtual field cannot be processed in static array constant!" assert
      ] [
        current isPlain [
          (current @processor getIrType " " current getPlainConstantIR) @result.catMany
          [
            currentTerminator: unfinishedTerminators.last;
            currentTerminator @result.cat
            currentTerminator ", " = ~
            @unfinishedTerminators.popBack
          ] loop
        ] [
          curVar: current getVar;
          curVar.data.getTag VarStruct = [
            (current @processor getIrType " ") @result.catMany
            struct: VarStruct curVar.data.get.get;
            struct.homogeneous ["[" makeStringView] ["{" makeStringView] if @result.cat
            first: TRUE dynamic;
            struct.fields.getSize [
              current: struct.fields.getSize 1 - i - struct.fields.at.refToVar;
              current isVirtual ~ [
                current @unfinishedVars.pushBack
                first [
                  struct.homogeneous ["]" makeStringView] ["}" makeStringView] if @unfinishedTerminators.pushBack
                  FALSE dynamic @first set
                ] [
                  ", " makeStringView @unfinishedTerminators.pushBack
                ] if
              ] when
            ] times
          ] [
            [FALSE] "Unknown type in static struct!" assert
          ] if
        ] if
      ] if

      TRUE
    ] &&
  ] loop

  result.size 2 - @result.@chars.shrink
  @result.makeZ
  result
];

makeVariableIRName: [
  refToVar: processor: block: ;;;
  var: @refToVar getVar;
  @var.host refToVar isGlobal ~ @processor block generateVariableIRNameWith @var.@irNameId set
];

findFieldWithOverloadDepth: [
  fieldNameInfo: refToVar: overloadDepth: processor: ; copy;;;

  var: refToVar getVar;

  result: {
    success: FALSE;
    index: -1;
  };

  var.data.getTag VarStruct = [
    struct: VarStruct var.data.get.get;
    i: struct.fields.dataSize copy dynamic;

    [
      i 0 > [
        i 1 - @i set

        i struct.fields.at .nameInfo fieldNameInfo = [
          overloadDepth 0 = [
            TRUE @result.@success set
            i @result.@index set
            FALSE
          ] [
            overloadDepth 1 - @overloadDepth set
            TRUE
          ] if
        ] [
          TRUE
        ] if
      ] &&
    ] loop
  ] [
    (refToVar @processor block getMplType " is not combined") assembleString @processor block compilerError
  ] if

  result
];

findField: [processor:; 0 dynamic @processor findFieldWithOverloadDepth];
