"control" use

"Array.Array" use
"String.addLog" use
"String.String" use
"String.StringView" use
"String.toString" use
"String.makeStringView" use
"Owner.Owner" use
"Variant.Variant" use
"Mref.Mref" use

Dirty:   [0n8 dynamic];
Dynamic: [1n8 dynamic];
Weak:    [2n8 dynamic];
Static:  [3n8 dynamic];
Virtual: [4n8 dynamic];
Schema:  [5n8 dynamic];

ShadowReasonNo:           [0];
ShadowReasonCapture:      [1];
ShadowReasonFieldCapture: [2];
ShadowReasonInput:        [3];
ShadowReasonField:        [4];
ShadowReasonPointee:      [5];

VarInvalid: [ 0 static];
VarCond:    [ 1 static];
VarNat8:    [ 2 static];
VarNat16:   [ 3 static];
VarNat32:   [ 4 static];
VarNat64:   [ 5 static];
VarNatX:    [ 6 static];
VarInt8:    [ 7 static];
VarInt16:   [ 8 static];
VarInt32:   [ 9 static];
VarInt64:   [10 static];
VarIntX:    [11 static];
VarReal32:  [12 static];
VarReal64:  [13 static];
VarCode:    [14 static];
VarBuiltin: [15 static];
VarImport:  [16 static];
VarString:  [17 static];
VarRef:     [18 static];
VarStruct:  [19 static];
VarEnd:     [20 static];

CodeNodeInfo: [{
  file:   ["File.FileSchema" use FileSchema] Mref;
  line:   Int32;
  column: Int32;
  index:  Int32;

  equal: [other:; index other.index =];
}];

Field: [{
  nameInfo: -1 dynamic; # NameInfo id
  nameOverload: -1 dynamic;
  refToVar: RefToVar;
}];

FieldArray: [Field Array];

Struct: [{
  fullVirtual:   FALSE dynamic;
  homogeneous:   FALSE dynamic;
  hasPreField:   FALSE dynamic;
  unableToDie:   FALSE dynamic;
  hasDestructor: FALSE dynamic;
  forgotten:     TRUE  dynamic;
  realFieldIndexes: Int32 Array;
  fields: FieldArray;
  structStorageSize: 0nx dynamic;
  structAlignment: 0nx dynamic;
}]; #IDs of pointee vars

RefToVar: [{
  data: Natx;

  var: [
    data 1nx ~ and @VarSchema addressToReference
  ];

  mutable: [
    data 1nx and 0nx = ~
  ];

  setVar: [
    newVar:;
    newVar VarSchema Ref same ~ ["variable expected" raiseStaticError] when
    newVar isConst ~ ["mutable variable expected" raiseStaticError] when
    address: newVar storageAddress;
    [address 1nx and 0nx =] "Address is not aligned!" assert
    address data 1nx and or !data
  ];

  setMutable: [
    copy newMutable:;
    newMutable [1nx] [0nx] if data 1nx ~ and or !data
  ];

  assigned: [var isNil ~];
  equal: [other:; var other.var is];
  hash: [address: var storageAddress; address 32n32 rshift address + Nat32 cast];
}];

Variable: [{
  VARIABLE: ();

  host:                              ["Block.BlockSchema" use @BlockSchema] Mref;
  mplNameId:                         -1 dynamic;
  irNameId:                          -1 dynamic;
  mplSchemaId:                       -1 dynamic;
  storageStaticity:                  Static;
  staticity:                         Static;
  global:                            FALSE dynamic;
  temporary:                         TRUE dynamic;
  usedInHeader:                      FALSE dynamic;
  capturedAsMutable:                 FALSE dynamic;
  capturedAsRealValue:               FALSE dynamic;
  tref:                              TRUE dynamic;
  shadowReason:                      ShadowReasonNo;
  globalId:                          -1 dynamic;
  shadowEventIndex:                  -1 dynamic;
  shadowBegin:                       RefToVar;
  shadowEnd:                         RefToVar;
  capturedHead:                      RefToVar;
  capturedTail:                      RefToVar;
  capturedPrev:                      RefToVar;
  realValue:                         RefToVar;
  globalDeclarationInstructionIndex: -1 dynamic;
  allocationInstructionIndex:        -1 dynamic;
  getInstructionIndex:               -1 dynamic;

  data: (
    Nat8             #VarInvalid
    Cond             #VarCond
    Nat64            #VarNat8
    Nat64            #VarNat16
    Nat64            #VarNat32
    Nat64            #VarNat64
    Nat64            #VarNatX
    Int64            #VarInt8
    Int64            #VarInt16
    Int64            #VarInt32
    Int64            #VarInt64
    Int64            #VarIntX
    Real64           #VarReal32
    Real64           #VarReal64
    CodeNodeInfo     #VarCode; id of node
    Int32            #VarBuiltin
    Int32            #VarImport
    String           #VarString
    RefToVar         #VarRef
    Struct Owner     #VarStruct
  ) Variant;

  INIT: [];
  DIE: [];
}];

schema VarSchema: Variable;

getVar: [
  refToVar:;
  [refToVar.assigned] "Wrong refToVar!" assert
  @refToVar.var
];

isVirtual: [
  refToVar:;

  var: refToVar getVar;
  var.staticity Virtual < ~
  [refToVar isVirtualType] ||
];

isSchema: [
  refToVar:;
  var: refToVar getVar;
  var.data.getTag VarRef = [var.staticity Schema =] &&
];

isVirtualType: [
  refToVar:;

  var: refToVar getVar;
  var.data.getTag VarBuiltin =
  [var.data.getTag VarCode =] ||
  [var.data.getTag VarStruct = [VarStruct var.data.get.get.fullVirtual copy] &&] ||
  [refToVar isSchema] ||
];
isInt: [
  var: getVar;
  var.data.getTag VarInt8 =
  [var.data.getTag VarInt16 =] ||
  [var.data.getTag VarInt32 =] ||
  [var.data.getTag VarInt64 =] ||
  [var.data.getTag VarIntX =] ||
];

isNat: [
  var: getVar;
  var.data.getTag VarNat8 =
  [var.data.getTag VarNat16 =] ||
  [var.data.getTag VarNat32 =] ||
  [var.data.getTag VarNat64 =] ||
  [var.data.getTag VarNatX =] ||
];

isAnyInt: [
  refToVar:;
  refToVar isInt
  [refToVar isNat] ||
];

isReal: [
  var: getVar;
  var.data.getTag VarReal32 =
  [var.data.getTag VarReal64 =] ||
];

isNumber: [
  refToVar:;
  refToVar isReal
  [refToVar isAnyInt] ||
];

isPlain: [
  refToVar:;
  refToVar isNumber [
    var: refToVar getVar;
    var.data.getTag VarCond =
  ] ||
];

isTinyArg: [
  refToVar:;
  refToVar isPlain [
    var: refToVar getVar;
    var.data.getTag VarRef =
  ] ||
];

isUnallocable: [
  var: getVar;
  var.data.getTag VarString =
  [var.data.getTag VarImport =] ||
];

isStruct: [
  var: getVar;
  var.data.getTag VarStruct =
];

isSingle: [
  isStruct ~
];

isAutoStruct: [
  refToVar:;
  var: refToVar getVar;
  var.data.getTag VarStruct =
  [VarStruct var.data.get.get.hasDestructor copy] &&
];

getVirtualValue: [
  refToVar:;
  recursive
  var: refToVar getVar;
  result: String;

  var.data.getTag (
    VarStruct [
      "{" @result.cat
      struct: VarStruct var.data.get.get;

      struct.fields.getSize [
        i 0 > ["," @result.cat] when
        i struct.fields.at .refToVar isVirtual ~ [
          i struct.fields.at .refToVar getVirtualValue @result.cat
        ] when
      ] times
      "}" @result.cat
    ]
    VarCode    [
      info: VarCode    var.data.get;
      ("\"" info.file.name getStringImplementation "\"/" info.line ":" info.column) @result.catMany
    ]
    VarBuiltin [VarBuiltin var.data.get @result.cat]
    VarRef     [
      pointee: VarRef var.data.get;
      pointeeVar: pointee getVar;
      var.staticity Schema = [
        "." @result.cat
      ] [
        pointeeVar.data.getTag (
          VarString  [
            string: VarString pointeeVar.data.get.getStringView;
            (string.size "_" string getStringImplementation) @result.catMany
          ]
          VarImport  [VarImport  pointeeVar.data.get @result.cat]
          [[FALSE] "Wrong type for virtual reference!" assert]
        ) case
      ] if
    ]
    [
      refToVar isPlain [
        refToVar getPlainConstantIR @result.cat
      ] [
        ("Tag = " var.data.getTag) addLog
        [FALSE] "Wrong type for virtual value!" assert
      ] if
    ]
  ) case

  result
];

getStringImplementation: [
  stringView:;
  [
    result: String;
    i: 0 dynamic;
    [
      i stringView.size < [
        codeRef: stringView.data i Natx cast + Nat8 addressToReference;
        code: codeRef copy;
        code 32n8 < ~ [code 127n8 <] && [code 34n8 = ~] && [code 92n8 = ~] && [  # exclude " and \
          code 0n32 cast @result.catSymbolCode
        ] [
          "\\" @result.cat
          code 16n8 < ["0"   @result.cat] when
          code @result.catHex
        ] if
        i 1 + @i set TRUE
      ] &&
    ] loop
    result
  ] call
];

isNonrecursiveType: [
  refToVar:;
  refToVar isPlain [
    var: refToVar getVar;
    var.data.getTag VarString =
    [var.data.getTag VarCode =] ||
    [var.data.getTag VarBuiltin =] ||
    [var.data.getTag VarImport =] ||
  ] ||
];

isSemiplainNonrecursiveType: [
  refToVar:;
  refToVar isPlain [
    var: refToVar getVar;
    var.data.getTag VarCode =
    [var.data.getTag VarBuiltin =] ||
    [var.data.getTag VarImport =] ||
  ] ||
];

getPlainConstantIR: [
  var: getVar;
  result: String;
  var.data.getTag VarCond = [
    VarCond var.data.get ["true" toString] ["false" toString] if @result set
  ] [
    var.data.getTag VarInt8 = [VarInt8 var.data.get toString @result set] [
      var.data.getTag VarInt16 = [VarInt16 var.data.get toString @result set] [
        var.data.getTag VarInt32 = [VarInt32 var.data.get toString @result set] [
          var.data.getTag VarInt64 = [VarInt64 var.data.get toString @result set] [
            var.data.getTag VarIntX = [VarIntX var.data.get toString @result set] [
              var.data.getTag VarNat8 = [VarNat8 var.data.get toString @result set] [
                var.data.getTag VarNat16 = [VarNat16 var.data.get toString @result set] [
                  var.data.getTag VarNat32 = [VarNat32 var.data.get toString @result set] [
                    var.data.getTag VarNat64 = [VarNat64 var.data.get toString @result set] [
                      var.data.getTag VarNatX = [VarNatX var.data.get toString @result set] [
                        var.data.getTag VarReal32 = [VarReal32 var.data.get 0.0r32 cast 0.0r64 cast bitView @result set] [
                          var.data.getTag VarReal64 = [VarReal64 var.data.get bitView @result set] [
                            ("Tag = " makeStringView var.data.getTag 0 cast) addLog
                            [FALSE] "Unknown plain struct while getting IR value" assert
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

  result
];

bitView: [
  copy f:;
  buffer: f storageAddress (0n8 0n8 0n8 0n8 0n8 0n8 0n8 0n8) addressToReference;
  result: String;
  "0x" @result.cat
  hexToStr: (
    "0" makeStringView "1" makeStringView "2" makeStringView "3" makeStringView "4" makeStringView
    "5" makeStringView "6" makeStringView "7" makeStringView "8" makeStringView "9" makeStringView
    "A" makeStringView "B" makeStringView "C" makeStringView "D" makeStringView "E" makeStringView "F" makeStringView);
  i: 0 dynamic;
  [
    i 0ix cast 0nx cast f storageSize < [
      d: f storageSize 0ix cast 0 cast i - 1 - buffer @ 0n32 cast;
      d 4n32 rshift 0 cast @hexToStr @ @result.cat
      d 15n32 and 0 cast @hexToStr @ @result.cat
      i 1 + @i set TRUE
    ] &&
  ] loop

  result
];

getSingleDataStorageSize: [
  refToVar: processor: ;;
  var: refToVar getVar;
  var.data.getTag (
    VarCond    [1nx]
    VarInt8    [1nx]
    VarInt16   [2nx]
    VarInt32   [4nx]
    VarInt64   [8nx]
    VarIntX    [processor.options.pointerSize 8nx /]
    VarNat8    [1nx]
    VarNat16   [2nx]
    VarNat32   [4nx]
    VarNat64   [8nx]
    VarNatX    [processor.options.pointerSize 8nx /]
    VarReal32  [4nx]
    VarReal64  [8nx]
    VarRef     [processor.options.pointerSize 8nx /]
    VarString  [
      0nx
    ]
    VarImport  [
      0nx
    ]
    [0nx]
  ) case
];

getStructStorageSize: [
  refToVar: processor: ;;
  var: refToVar getVar;
  struct: VarStruct var.data.get.get;
  struct.structStorageSize copy
];


getStorageSize: [
  refToVar: processor: ;;
  refToVar isSingle [
    refToVar @processor getSingleDataStorageSize
  ] [
    refToVar @processor getStructStorageSize
  ] if
];

getStructAlignment: [
  refToVar: processor: ;;
  var: refToVar getVar;
  struct: VarStruct var.data.get.get;
  struct.structAlignment copy
];

getAlignment: [
  refToVar: processor: ;;
  refToVar isSingle [
    refToVar @processor getSingleDataStorageSize
  ] [
    refToVar @processor getStructAlignment
  ] if
];

makeStringId: [
  string: processor: ;;
  fr: string @processor.@nameTable.find;
  fr.success [
    fr.value copy
  ] [
    result: processor.nameBuffer.dataSize copy;
    string makeStringView result @processor.@nameTable.insert
    @string move @processor.@nameBuffer.pushBack
    result
  ] if
];

markAsUnableToDie: [
  refToVar:;
  var: @refToVar getVar;
  var.data.getTag VarStruct = [TRUE VarStruct @var.@data.get.get.@unableToDie set] when
];

isForgotten: [
  refToVar:;
  var: refToVar getVar;
  var.data.getTag VarStruct = [
    VarStruct var.data.get.get.forgotten copy
  ] [
    FALSE
  ] if
];

variablesAreSame: [
  refToVar1:;
  refToVar2:;
  refToVar1 getVar.mplSchemaId refToVar2 getVar.mplSchemaId = # id compare better than string compare!
];

staticityOfVar: [
  refToVar:;
  var: refToVar getVar;
  var.staticity copy
];

fullUntemporize: [
  refToVar:;
  var: @refToVar getVar;
  FALSE @var.@temporary set
  var.data.getTag VarStruct = [
    FALSE VarStruct @var.@data.get.get.@forgotten set
  ] when
];
