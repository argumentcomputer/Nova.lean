import Lake
open Lake DSL

package Nova

@[default_target]
lean_lib Nova

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "7ef2fdec4176c6cd01cfd6891ca5ed07de2848d9"
