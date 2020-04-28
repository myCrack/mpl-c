"control" use

"String.String" use
"Mref.Mref" use

File: [{
  name: String;
  text: String;
  debugId: Int32;
  rootBlock: ["Block.BlockSchema" use BlockSchema] Mref;
}];

schema FileSchema: File;
