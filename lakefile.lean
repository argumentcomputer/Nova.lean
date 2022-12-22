import Lake
open Lake DSL

package Nova

@[default_target]
lean_lib Nova

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "dcf9c9f77db7564025f61107e9503caf011e39dc"

require BellaNova from git
  "https://github.com/yatima-inc/Bellanova.lean" @ "1e06e09018ec40580e47165dabe0dd7d1ff8eef9"