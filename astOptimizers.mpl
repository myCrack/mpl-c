"Array" use
"Owner" use
"String" use
"control" use

"astNodeType" use

optimizeLabels: [
  parserResult:;

  @parserResult.@memory [
    currentIndexArray:;

    newIndexArray: AstNodeArray;
    @currentIndexArray.@positionInfo move @newIndexArray.@positionInfo set

    @currentIndexArray.@nodes [
      current:;
      current.data.getTag AstNodeType.Label = [
        AstNodeType.Label current.data.get.children @parserResult.@memory.at.@nodes [
          move @newIndexArray.@nodes.pushBack
        ] each
      ] when

      @current move @newIndexArray.@nodes.pushBack
    ] each

    @newIndexArray move @currentIndexArray set
  ] each
];

optimizeNamesInCurrentNode: [
  node:;

  optimizeName: [
    nameWithInfo:;
    nameIndex: nameWithInfo.name makeStringView @nameManager.createName;
    nameIndex @nameWithInfo.@nameInfo set
  ];

  (
    AstNodeType.Label           [optimizeName] # must not have children, it must be after label optimizing
    AstNodeType.Name            [optimizeName]
    AstNodeType.NameRead        [optimizeName]
    AstNodeType.NameWrite       [optimizeName]
    AstNodeType.NameMember      [optimizeName]
    AstNodeType.NameReadMember  [optimizeName]
    AstNodeType.NameWriteMember [optimizeName]
  ) @node.@data.visit
];

optimizeNames: [
  parserResult: nameManager: ;;

  @parserResult.@memory [
    .@nodes [
      optimizeNamesInCurrentNode
    ] each
  ] each
];

concatParserResult: [
  mresult:;
  current:;
  shift: mresult.memory.getSize;

  adjustArray: [
    astArrayIndex:;
    astArrayIndex shift + @astArrayIndex set
  ];

  @current.@root adjustArray

  @current.@memory [
    currentArray:;
    @currentArray.@nodes [
      currentNode:;

      currentNode.data.getTag AstNodeType.Code = [
        AstNodeType.Code @currentNode.@data.get adjustArray
      ] [
        currentNode.data.getTag AstNodeType.List = [
          AstNodeType.List @currentNode.@data.get adjustArray
        ] [
          currentNode.data.getTag AstNodeType.Object = [
            AstNodeType.Object @currentNode.@data.get adjustArray
          ] when
        ] if
      ] if
    ] each

    @currentArray move @mresult.@memory.pushBack
  ] each

  current.root @mresult.@roots.pushBack
];
