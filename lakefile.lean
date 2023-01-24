import Lake
open Lake DSL

package Nova

@[default_target]
lean_lib Nova

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "49ee890897dbdd4665d0e8c75cd3401f0b4e6f21"

require BellaNova from git
  "https://github.com/yatima-inc/Bellanova.lean" @ "885f12bfb39620c8130498925ed948533650cbb3"

require FF from git
  "https://github.com/yatima-inc/FF.lean" @ "7ac28e1ab71635bdf1ba092ccedba29636b99016"
