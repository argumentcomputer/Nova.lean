import Lake
open Lake DSL

package Nova

@[default_target]
lean_lib Nova

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "533d71efa5853ff014f42c174d6321d74251209f"

require BellaNova from git
  "https://github.com/yatima-inc/Bellanova.lean" @ "885f12bfb39620c8130498925ed948533650cbb3"

require FF from git
  "https://github.com/yatima-inc/FF.lean" @ "5a9b8eeb9a6438fe6bcfcb84f60329f888e7b95f"
