import Lake
open Lake DSL

package «qrh-proof» where

lean_lib «QRH» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
