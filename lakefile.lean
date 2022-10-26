import Lake
open Lake DSL

package Nova

@[defaultTarget]
lean_lib Nova

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "11336e502174b1449f525b1e44d76f6a44fbd274"