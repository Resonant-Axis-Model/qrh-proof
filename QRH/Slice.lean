import Mathlib
import QRH.Prelude

namespace QRH

open Complex
open scoped ComplexConjugate

noncomputable section

/-- Points on the quaternionic slice spanned by `1` and `Quaternion.i`. -/
structure SlicePoint where
  /-- Real part along the slice. -/
  rePart : ℝ
  /-- Imaginary part along the fixed direction `Quaternion.i`. -/
  imPart : ℝ

namespace SlicePoint

/-- View a slice point as a quaternion `a + b⋅i`. -/
@[simp] def toQuat (p : SlicePoint) : ℍ :=
  ⟨p.rePart, p.imPart, 0, 0⟩

instance : Coe SlicePoint ℍ := ⟨toQuat⟩

@[simp] lemma re_coe (p : SlicePoint) : re (p : ℍ) = p.rePart := rfl
@[simp] lemma imI_coe (p : SlicePoint) : (p : ℍ).imI = p.imPart := rfl
@[simp] lemma imJ_coe (p : SlicePoint) : (p : ℍ).imJ = 0 := rfl
@[simp] lemma imK_coe (p : SlicePoint) : (p : ℍ).imK = 0 := rfl

/-- Chart from the slice to the complex plane. -/
@[simp] def chart (p : SlicePoint) : ℂ := Complex.mk p.rePart p.imPart

/-- Embed a complex number as a slice point. -/
@[simp] def ofComplex (z : ℂ) : SlicePoint :=
  ⟨z.re, z.im⟩

@[simp] lemma chart_ofComplex (z : ℂ) : chart (ofComplex z) = z := by
  cases z
  simp [ofComplex, chart]

@[simp] lemma coe_ofComplex (z : ℂ) : (ofComplex z : ℍ) = ⟨z.re, z.im, 0, 0⟩ := rfl

/-- Reconstruct a slice point from a quaternion whose `j,k` parts vanish. -/
@[simp] def ofQuat (q : ℍ) (_ : q.imJ = 0) (_ : q.imK = 0) : SlicePoint :=
  ⟨q.re, q.imI⟩

/-- Slice reflection induced by the global involution `J`. -/
def reflect (p : SlicePoint) : SlicePoint :=
  ⟨1 - p.rePart, p.imPart⟩

@[simp] lemma coe_reflect (p : SlicePoint) :
    (reflect p : ℍ) = J (p : ℍ) := by
  ext <;> simp [reflect, J, sub_eq_add_neg]

@[simp] lemma chart_reflect (p : SlicePoint) :
    chart (reflect p) = 1 - conj (chart p) := by
  refine Complex.ext ?hre ?him
  · simp [reflect, chart]
  · simp [reflect, chart]

end SlicePoint

end

end QRH
