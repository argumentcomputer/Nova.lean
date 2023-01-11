import Lake
open Lake DSL

package Nova

@[default_target]
lean_lib Nova

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "704823e421b333ea9960347e305c60f654618422"

require BellaNova from git
  "https://github.com/yatima-inc/Bellanova.lean" @ "a262858693fe7e6beb4f6aeb828ba41d557c76dc"

require FF from git
  "https://github.com/yatima-inc/FF.lean.git" @ "9d86277cf2b291151aa5226d97f8db038a413a0c"
