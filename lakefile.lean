import Lake
open Lake DSL

package «qrh» where
  moreLeanArgs := #[]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "stable"

@[default_target]
lean_lib QRH
