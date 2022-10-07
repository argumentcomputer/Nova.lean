import Lake
open Lake DSL

package Nova

@[defaultTarget]
lean_lib Nova

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "3cb5f4706cd49c1803cdb7a5aec53ca58e8a8b1a"