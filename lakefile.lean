import Lake
open Lake DSL

package Nova

@[default_target]
lean_lib Nova

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "ff0b553a7c2a63d3b0b9c963dfdeebea2a692a10"

require BellaNova from git
  "https://github.com/yatima-inc/Bellanova.lean" @ "30912b7ab0c1394eb387b0a503f9af2400a01733"

require FF from git
  "https://github.com/yatima-inc/FF.lean" @ "dcedbe5f66dfb6d28f81a1523d14dce227e9197e"
