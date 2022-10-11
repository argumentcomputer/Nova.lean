import Lake
open Lake DSL

package Nova

@[defaultTarget]
lean_lib Nova

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "f22f6d6aade10f3da41d2bce1086794b40c34d97"