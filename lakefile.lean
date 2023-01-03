import Lake
open Lake DSL

package Nova

@[default_target]
lean_lib Nova

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "515b7eff7765dcf55ce275ac41fa13a30a59f1d0"

require BellaNova from git
  "https://github.com/yatima-inc/Bellanova.lean" @ "5d987647b624e178a24d19bfeed982b8cccc3a1d"
