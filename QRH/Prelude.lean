/-
  Prelude: convenient aliases and basic quaternion facts we’ll use.
-/
import Mathlib

namespace QRH

noncomputable section

-- Alias ℍ for real-quaternions from mathlib4
notation "ℍ" => Quaternion ℝ

-- Real part shortcut
@[simp] def re (q : ℍ) : ℝ := q.re

-- Conjugation shortcut
@[simp] def conj (q : ℍ) : ℍ := star q

-- Unit quaternion predicate (S³ ⊂ ℍ)
def isUnitQuat (q : ℍ) : Prop := q.normSq = 1

-- The standard SU(2)≃S³ viewpoint is background; we only need the subset predicate here.

-- Useful involution: J q := 1 - conj q
@[simp] def J (q : ℍ) : ℍ := (1 : ℍ) - conj q

lemma J_involutive : Function.Involutive J := by
  intro q
  unfold J
  simp [conj, sub_eq_add_neg]

/-- Real part under J flips about 1/2. -/
lemma re_J (q : ℍ) : re (J q) = 1 - re q := by
  unfold J re
  have h := Quaternion.re_sub (1 : ℍ) (star q)
  have hconj : (star q).re = q.re := Quaternion.re_star q
  -- Linter prefers `simp` for this final rewrite.
  simp [conj, hconj]

attribute [-simp] QRH.J

@[simp] lemma normSq_mul (a b : ℍ) :
    Quaternion.normSq (a * b) = Quaternion.normSq a * Quaternion.normSq b :=
  (map_mul Quaternion.normSq a b : _)

@[simp] lemma normSq_one : Quaternion.normSq (1 : ℍ) = 1 :=
  (map_one Quaternion.normSq : _)

@[simp] lemma normSq_conj (q : ℍ) : Quaternion.normSq (conj q) = Quaternion.normSq q := by
  simp [conj]

lemma normSq_unit_of_mul_conj_eq_one {U : ℍ}
    (hU : U * conj U = (1 : ℍ)) : Quaternion.normSq U = 1 := by
  have hmul := congrArg Quaternion.normSq hU
  have hsq : (Quaternion.normSq U) ^ 2 = (1 : ℝ) ^ 2 := by
    simpa [pow_two, normSq_mul, normSq_conj, normSq_one] using hmul
  have hnonneg : 0 ≤ Quaternion.normSq U := Quaternion.normSq_nonneg (a := U)
  have hcases :=
    (sq_eq_sq_iff_eq_or_eq_neg
      (a := Quaternion.normSq U) (b := (1 : ℝ))).mp hsq
  rcases hcases with hpos | hneg
  · exact hpos
  · have : False := by
      have : (0 : ℝ) ≤ -1 := by simpa [hneg] using hnonneg
      linarith
    exact this.elim

lemma one_sub_J (q : ℍ) : (1 : ℍ) - J q = conj q := by
  unfold J
  simp [sub_eq_add_neg]

@[simp] lemma conj_mk (a b c d : ℝ) :
    conj (⟨a, b, c, d⟩ : ℍ) = (⟨a, -b, -c, -d⟩ : ℍ) := by
  ext <;> simp [conj]

@[simp] lemma re_mk (a b c d : ℝ) :
    re (⟨a, b, c, d⟩ : ℍ) = a := by
  -- `re` is just the real component of the quaternion.
  rfl

end

end QRH
