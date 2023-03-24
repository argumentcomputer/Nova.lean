import Lake
open Lake DSL

package Nova

@[default_target]
lean_lib Nova

require YatimaStdLib from git
  "https://github.com/lurk-lab/YatimaStdLib.lean" @ "533d71efa5853ff014f42c174d6321d74251209f"

require BellaNova from git
  "https://github.com/lurk-lab/Bellanova.lean" @ "885f12bfb39620c8130498925ed948533650cbb3"

require FFaCiL from git
  "https://github.com/lurk-lab/FFaCiL.lean" @ "9a4c77f8b703b60ae4e353b957e858a2e1de2e83"
