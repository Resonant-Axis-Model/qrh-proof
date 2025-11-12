import Mathlib
import QRH.Prelude
import QRH.Factorial
import QRH.Coherence

open QRH

/-- Top-level statement of the framework: Under conjugation/J symmetries of ⊙ and
    convex-symmetric fibers for C(q)=‖⊙(q)(1−q)‖², any stationary real-fiber point
    satisfies Re(q)=1/2. -/
example (x y z a : ℝ) [FiberConvexSymm]
  (h : IsLocalMin (CAlong x y z) a) : a = (1:ℝ)/2 := by
  simpa using QRH.stationary_implies_re_half (x:=x) (y:=y) (z:=z) (a:=a) h
