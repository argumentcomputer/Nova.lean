import Lake
open Lake DSL

package Nova

@[default_target]
lean_lib Nova

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "649368d593f292227ab39b9fd08f6a448770dca8"

require BellaNova from git
  "https://github.com/yatima-inc/Bellanova.lean" @ "32faf6c111759e7ddda187b07d48c7ca00964a9e"

require FF from git
  "https://github.com/yatima-inc/FF.lean" @ "3fa1117d152d9842b74f7b197f0d93fbdb6c32f2"
