import Mathlib
import Mathlib.NumberTheory.LSeries.RiemannZeta
import QRH.Prelude
import QRH.Coherence
import QRH.Slice

namespace QRH

open Complex
open scoped Real ComplexConjugate

noncomputable section

/-- Canonical chart `φ : ℍ → ℂ` selecting the slice spanned by `1` and `Quaternion.i`. -/
@[simp] def phi (q : ℍ) : ℂ :=
  Complex.mk (re q) q.imI

@[simp] lemma phi_ofSlice (p : SlicePoint) : phi (p : ℍ) = SlicePoint.chart p := by
  cases p with
  | mk rePart imPart =>
      simp [phi, SlicePoint.chart, SlicePoint.toQuat]

@[simp] lemma phi_reflect (p : SlicePoint) :
    phi (SlicePoint.reflect p : ℍ) = 1 - conj (phi (p : ℍ)) := by
  have := SlicePoint.chart_reflect p
  simpa [phi_ofSlice, SlicePoint.coe_reflect]
    using this

/-- Abstract interface encoding the classical `ζ`, `Γ`, and completed `ξ` data. -/
structure ClassicalXiData where
  /-- Riemann zeta on the complex plane. -/
  zeta : ℂ → ℂ
  /-- Completed xi-function satisfying `xi(s) = xi(1 - s)`. -/
  xi : ℂ → ℂ
  /-- Functional equation for the completed xi-function. -/
  functional_eq : ∀ s : ℂ, xi s = xi (1 - s)

namespace ClassicalXiData

@[simp] def xiSlice (h : ClassicalXiData) (p : SlicePoint) : ℂ :=
  h.xi (SlicePoint.chart p)

lemma xiSlice_eq_phi (h : ClassicalXiData) (p : SlicePoint) :
    h.xiSlice p = h.xi (phi (p : ℍ)) := by
  simpa [ClassicalXiData.xiSlice, phi_ofSlice]

@[simp] def zetaSlice (h : ClassicalXiData) (p : SlicePoint) : ℂ :=
  h.zeta (SlicePoint.chart p)

end ClassicalXiData

/-- The concrete (ζ, ξ) data coming from mathlib's definitions. -/
@[simp] def classicalXiDataRiemann : ClassicalXiData where
  zeta := riemannZeta
  xi := completedRiemannZeta
  functional_eq := by
    intro s
    have := completedRiemannZeta_one_sub (1 - s)
    -- `completedRiemannZeta (1 - (1 - s)) = completedRiemannZeta (1 - s)`
    simpa using this

/-- Bombieri's specialization `ξ(t) = ξ(1/2 + it)` viewed as a complex function. -/
@[simp] def bombieriXi (t : ℂ) : ℂ :=
  completedRiemannZeta ((1 : ℂ) / 2 + Complex.I * t)

@[simp] lemma bombieriXi_neg (t : ℂ) : bombieriXi (-t) = bombieriXi t := by
  unfold bombieriXi
  have hreflect :
      (1 : ℂ) / 2 + Complex.I * (-t) = 1 - ((1 : ℂ) / 2 + Complex.I * t) := by
    ring
  simpa [hreflect] using
    completedRiemannZeta_one_sub ((1 : ℂ) / 2 + Complex.I * t)

/-- Bombieri's analytic restatement of RH: every zero of the ξ-function along
    `s = 1/2 + it` occurs for a real parameter `t`. -/
def BombieriHypothesis : Prop :=
  ∀ t : ℂ, bombieriXi t = 0 → t.im = 0

lemma gamma_ne_zero_of_nontrivial_zero {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) :
    Complex.Gammaℝ s ≠ 0 := by
  intro hγ
  obtain ⟨n, hn⟩ := (Gammaℝ_eq_zero_iff (s := s)).1 hγ
  cases n with
  | zero =>
      have : riemannZeta 0 = 0 := by simpa [hn] using hz
      simpa [riemannZeta_zero] using this
  | succ m =>
      have : s = -2 * (m + 1) := by
        simpa [Nat.cast_succ, add_comm, add_left_comm, add_assoc] using hn
      exact htriv ⟨m, this⟩

lemma completed_zero_of_nontrivial_zero {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) :
    completedRiemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro hs
    have : riemannZeta 0 = 0 := by simpa [hs] using hz
    simpa [riemannZeta_zero] using this
  have hΓ := gamma_ne_zero_of_nontrivial_zero hz htriv
  have hrel := riemannZeta_def_of_ne_zero (s:=s) hs0
  have hmul :
      completedRiemannZeta s = riemannZeta s * Complex.Gammaℝ s := by
    have := congrArg (fun z : ℂ => z * Complex.Gammaℝ s) hrel
    simpa [mul_comm, mul_left_comm, mul_assoc] using this.symm
  simpa [hz, mul_comm, mul_left_comm, mul_assoc] using hmul

lemma critical_param_eq (s : ℂ) :
    (1 : ℂ) / 2 + Complex.I * (-Complex.I * (s - (1 : ℂ) / 2)) = s := by
  have hmul :
      Complex.I * (-Complex.I * (s - (1 : ℂ) / 2)) =
        s - (1 : ℂ) / 2 := by
    simp [mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg, Complex.I_mul_I]
  simpa [hmul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

lemma im_negI_mul_sub_half (s : ℂ) :
    (-(Complex.I) * (s - (1 : ℂ) / 2)).im = (1 : ℝ) / 2 - s.re := by
  simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]

lemma bombieri_im_zero_of_nontrivial_zero
    (hB : BombieriHypothesis) {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) :
    s.re = (1 : ℝ) / 2 := by
  set t := -Complex.I * (s - (1 : ℂ) / 2)
  have hcomp : completedRiemannZeta s = 0 :=
    completed_zero_of_nontrivial_zero hz htriv
  have hxi : bombieriXi t = 0 := by
    change completedRiemannZeta ((1 : ℂ) / 2 + Complex.I * t) = 0
    simpa [t, critical_param_eq s] using hcomp
  have ht : t.im = 0 := hB t hxi
  have hproj : (1 : ℝ) / 2 - s.re = 0 := by
    simpa [t, im_negI_mul_sub_half] using ht
  exact (sub_eq_zero.mp hproj).symm

lemma BombieriHypothesis.to_RiemannHypothesis
    (hB : BombieriHypothesis) :
    RiemannHypothesis := by
  intro s hz htriv hs1
  simpa using
    bombieri_im_zero_of_nontrivial_zero hB hz htriv

/-- Calibration that relates quaternionic coherence to the classical `|ξ|^2` on the slice. -/
structure SliceCoherenceCalibration (hQ : QFacHypotheses)
    (hXi : ClassicalXiData) where
  /-- Positive scale factor linking `C` and `|ξ|²`. -/
  scale : ℝ
  scale_pos : 0 < scale
  calibration :
    ∀ p : SlicePoint, C (p : ℍ) = scale * Complex.normSq (hXi.xiSlice p)

namespace SliceCoherenceCalibration

lemma calibration_via_phi {hQ : QFacHypotheses} {hXi : ClassicalXiData}
    (H : SliceCoherenceCalibration hQ hXi) :
    ∀ p : SlicePoint, C (p : ℍ) =
      H.scale * Complex.normSq (hXi.xi (phi (p : ℍ))) := by
  intro p
  simpa [ClassicalXiData.xiSlice, phi_ofSlice] using H.calibration p

end SliceCoherenceCalibration

end QRH
