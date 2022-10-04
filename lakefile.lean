import Lake
open Lake DSL

package Nova

@[defaultTarget]
lean_lib Nova

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "868abcb58c5d96927c65ac304ee1e99a21d57457"