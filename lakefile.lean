import Lake
open Lake DSL

package Nova

@[default_target]
lean_lib Nova

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "818538aced05fe563ef95bb3dcdf5ed755896139"

require BellaNova from git
  "https://github.com/yatima-inc/Bellanova.lean" @ "efa3c8d50744ee92f7c47d145b78020f5793cc73"