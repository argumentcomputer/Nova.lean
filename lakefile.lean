import Lake
open Lake DSL

package Nova

@[defaultTarget]
lean_lib Nova

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "07148ba7c40a163260cd7b3e1c76fd5ac964cb75"