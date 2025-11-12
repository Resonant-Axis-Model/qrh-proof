/-
  Quaternionic Factorial Operator ⊙ (axiomatized interface).
  We introduce a symbol `qfac : ℍ → ℍ` standing for the operator
  ⊙(q) = ∫₀^∞ e^{-x} e^{q log x} dx,
  and record the two key symmetries we need for the coherence argument.
-/
import Mathlib
import QRH.Prelude

namespace QRH

/-- Quaternionic Factorial Operator (axiomatized). -/
axiom qfac : ℍ → ℍ

/-- All analytic assumptions about `qfac` are bundled so lemmas can state them explicitly. -/
structure QFacHypotheses : Prop where
  qfac_conj : ∀ q : ℍ, qfac (conj q) = conj (qfac q)
  qfac_J_unit_transport :
    ∀ q : ℍ, ∃ U : ℍ, U * conj U = 1 ∧
      qfac (J q) = qfac q * U ∧
      ((1 : ℍ) - J q) = conj U * ((1 : ℍ) - q)
  coherence_balance :
    ∀ q : ℍ,
      Quaternion.normSq (qfac (J q) * ((1 : ℍ) - J q)) =
        Quaternion.normSq (qfac q * ((1 : ℍ) - q))

end QRH
