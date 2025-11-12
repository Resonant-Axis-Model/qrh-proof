/-
  Coherence functional and orbit symmetry.
  C(q) := ‖ ⊙(q) · (1 - q) ‖^2
  We prove: C is J-invariant and characterize fixed points of J
  as exactly the Re(q)=1/2 slice. Then, under a convexity-on-fibers
  hypothesis, any stationary point along a fixed imaginary fiber occurs
  at Re(q)=1/2.

  ─────────────────────────────────────────────────────────────────────
  Plain-English map to the six “Quaternionic Riemann” equations:

  1. Quaternionic rotation form (S³ geometry and the involution J):
     The definitions imported from `QRH.Prelude` give the 4-D rotational
     setting and the reflection J(q) = 1 - conj q that acts on S³.

  2. Quaternionic factorial operator:
     `qfac : ℍ → ℍ` stands for ⊙(q); we do not compute it, but assume
     one symmetry axiom (`qfac_coherence_balance`) capturing the
     reflection invariance of the coherence functional.

  3. Conjugate self-symmetry:
     `re_half_fixed` and `J_fixed_iff_re_half` formalize that J fixes
     exactly the mid-slice Re(q) = 1/2, matching the “self-balanced”
     quaternions.

  4. Coherence functional:
     `C q = ‖⊙(q)(1 - q)‖²` together with the axiom shows `C (J q) = C q`,
     so the coherence is invariant under the conjugate reflection.

  5. Slice ↔ classical chart:
     `QRH.Slice` fixes a quaternionic slice and a chart `φ` landing in ℂ,
     so the quaternionic reflection corresponds to `s ↦ 1 - conj(s)` in
     classical variables.

  6. Pulling back ζ/ξ:
     `QRH.ZetaBridge` bundles the classical ζ/ξ and functional equation;
     a calibration hypothesis states `C(q)` matches `|ξ(φ(q))|²` on the
     slice, letting “stationary ⇒ mid-slice” translate to the classical
     critical line `Re(s)=1/2`.

  7. Stationary condition:
     The class `FiberConvexSymm` encodes the convexity-along-fibers
     hypothesis; using it we prove stationary ⇒ Re(q)=1/2.

  8. Geometric interpretation:
     Putting everything together, the only equilibrium (stationary)
     points for the coherence functional lie on the quaternionic
     critical slice Re(q) = 1/2—the pulled-back version of the
     classical RH critical line.
  ─────────────────────────────────────────────────────────────────────
-/
import Mathlib
import QRH.Prelude
import QRH.Factorial

namespace QRH

open scoped Real Topology
noncomputable section

/-- Coherence functional. -/
@[simp] def C (q : ℍ) : ℝ :=
  Quaternion.normSq (qfac q * ((1 : ℍ) - q))

lemma C_expand (q : ℍ) :
  C q = Quaternion.normSq (qfac q) * Quaternion.normSq ((1 : ℍ) - q) := by
  simp [C, normSq_mul]

/-- J-invariance of the coherence functional, using the recorded symmetries. -/
lemma C_J_invariant (q : ℍ) (hQ : QFacHypotheses) : C (J q) = C q := by
  simpa [C] using hQ.coherence_balance q

lemma re_half_fixed (q : ℍ) (h : re q = (1 : ℝ) / 2) : J q = q := by
  cases q with
  | mk a b c d =>
      have hhalf : 1 - a = a := by
        have ha : a = (1 : ℝ) / 2 := by simpa [re, re_mk] using h
        have : (1 : ℝ) - (1 : ℝ) / 2 = (1 : ℝ) / 2 := by norm_num
        simpa [ha] using this
      have hJ : J (⟨a, b, c, d⟩ : ℍ) = (⟨1 - a, b, c, d⟩ : ℍ) := by
        ext <;> simp [J, sub_eq_add_neg]
      have hsame : (⟨1 - a, b, c, d⟩ : ℍ) = (⟨a, b, c, d⟩ : ℍ) := by
        simp [hhalf]
      exact hJ.trans hsame

/-- Fixed points of J are precisely the mid-slice Re(q)=1/2. -/
lemma J_fixed_iff_re_half (q : ℍ) : J q = q ↔ re q = (1 : ℝ)/2 := by
  constructor
  · intro h
    -- Taking real parts and using re_J: re(q) = re(J q) = 1 - re(q)
    have hq : re (J q) = re q := by
      simpa using congrArg re h
    have hmid : re q = 1 - re q := by
      exact hq.symm.trans (re_J q)
    have : re q = (1 : ℝ) / 2 := by
      linarith [hmid]
    simpa [this]
  · intro h
    -- Defer the geometrically-motivated direction to the `re_half_fixed` axiom.
    exact re_half_fixed q h

/-- For each fixed imaginary triple (x,y,z), define the real-fiber function. -/
@[simp] def CAlong (x y z : ℝ) (a : ℝ) : ℝ :=
  C (⟨a, x, y, z⟩ : ℍ)

@[simp] lemma J_on_components (a x y z : ℝ) :
    J (⟨a, x, y, z⟩ : ℍ) = (⟨1 - a, x, y, z⟩ : ℍ) := by
  ext <;> simp [J, sub_eq_add_neg]

lemma CAlong_symm_half (x y z a : ℝ) (hQ : QFacHypotheses) :
    CAlong x y z a = CAlong x y z (1 - a) := by
  unfold CAlong
  have h := C_J_invariant (⟨a, x, y, z⟩ : ℍ) hQ
  simpa only [J_on_components] using h.symm

/-- Hypothesis: along each imaginary fiber (x,y,z) the function a ↦ CAlong x y z a
    is (i) symmetric about a=1/2 and (ii) strictly convex, so any stationary point
    occurs at a=1/2 and is the unique minimizer. -/
class FiberConvexSymm : Prop where
  strictConvex_stationary_at_half :
      ∀ x y z a, IsLocalMin (CAlong x y z) a → a = (1 : ℝ) / 2

/-- Analytic convexity hypothesis: each fiber function `a ↦ CAlong x y z a`
    is strictly convex on ℝ, as predicted by the AGQF/⊙ analysis. -/
class FiberStrictConvex : Prop where
  strictConvex :
      ∀ x y z, StrictConvexOn ℝ Set.univ (fun a => CAlong x y z a)

private lemma perturb_eq (a t : ℝ) :
    (1 - t) * a + t * (1 - a) - a = t * (1 - 2 * a) := by
  ring

private lemma perturb_dist (a t : ℝ) (ht : 0 ≤ t) :
    |(1 - t) * a + t * (1 - a) - a| = t * |1 - 2 * a| := by
  simpa [perturb_eq, abs_mul, abs_of_nonneg ht]

private lemma symmetric_strictConvex_localMin_eq_half
    {f : ℝ → ℝ}
    (hsymm : ∀ a, f a = f (1 - a))
    (hstrict : StrictConvexOn ℝ Set.univ f) :
    ∀ ⦃a⦄, IsLocalMin f a → a = (1 : ℝ) / 2 := by
  intro a hmin
  classical
  have hmem : {x : ℝ | f a ≤ f x} ∈ 𝓝 a := hmin
  by_contra hneq
  set b := 1 - a
  have hb : f b = f a := by
    simpa [b] using (hsymm a).symm
  have hneq' : a ≠ b := by
    intro h
    have hsum : a = 1 - a := by simpa [b] using h
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    have : 2 * a = (1 : ℝ) := by linarith [hsum]
    have : a = (1 : ℝ) / 2 := by
      have := congrArg (fun x : ℝ => x / (2 : ℝ)) this
      simpa [htwo] using this
    exact hneq this
  have hden_ne : 1 - 2 * a ≠ 0 := by
    intro hzero
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    have : 2 * a = (1 : ℝ) := by linarith [hzero]
    have : a = (1 : ℝ) / 2 := by
      have := congrArg (fun x : ℝ => x / (2 : ℝ)) this
      simpa [htwo] using this
    exact hneq this
  have hden_pos : 0 < |1 - 2 * a| := abs_pos.mpr hden_ne
  obtain ⟨ε, εpos, hball⟩ := Metric.mem_nhds_iff.mp hmem
  have hcoeff : 0 < ε / (2 * |1 - 2 * a|) := by
    have hpos : 0 < 2 * |1 - 2 * a| :=
      mul_pos (by norm_num : (0 : ℝ) < 2) hden_pos
    exact div_pos εpos hpos
  have htPos : 0 < min (ε / (2 * |1 - 2 * a|)) (1 / 2 : ℝ) :=
    lt_min hcoeff (by norm_num)
  let t := min (ε / (2 * |1 - 2 * a|)) (1 / 2 : ℝ)
  have ht_pos : 0 < t := by simpa [t] using htPos
  have ht_le_half : t ≤ (1 / 2 : ℝ) := min_le_right _ _
  have ht_lt_one : t < 1 := by
    have hhalf : (1 / 2 : ℝ) < 1 := by norm_num
    exact lt_of_le_of_lt ht_le_half hhalf
  have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
  have ht_le_frac : t ≤ ε / (2 * |1 - 2 * a|) := min_le_left _ _
  set x0 := (1 - t) * a + t * b
  have hdist : dist x0 a < ε := by
    have hxabs : |x0 - a| = t * |1 - 2 * a| := by
      have := perturb_dist a t ht_nonneg
      simpa [x0, b] using this
    have hxle : |x0 - a| ≤ ε / 2 := by
      have hpos_den : 0 ≤ |1 - 2 * a| := abs_nonneg _
      have hmul :=
        mul_le_mul_of_nonneg_right ht_le_frac hpos_den
      have htwo : (2 : ℝ) ≠ 0 := by norm_num
      have hden_ne_zero : |1 - 2 * a| ≠ 0 := ne_of_gt hden_pos
      have hrewrite :
          (ε / (2 * |1 - 2 * a|)) * |1 - 2 * a| = ε / 2 := by
        field_simp [htwo, hden_ne_zero, mul_comm, mul_left_comm, mul_assoc]
      have hbound :
          t * |1 - 2 * a| ≤ ε / 2 := by
        simpa [hrewrite] using hmul
      simpa [hxabs] using hbound
    have hhalf_lt : ε / 2 < ε := half_lt_self εpos
    have : |x0 - a| < ε := lt_of_le_of_lt hxle hhalf_lt
    simpa [Real.dist_eq, abs_sub_comm] using this
  have hxmem : x0 ∈ Metric.ball a ε := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hdist
  have hx_ge : f a ≤ f x0 := hball hxmem
  have hx_lt : f x0 < f a := by
    have hstrict' :=
      hstrict.2 (by simp) (by simp) hneq' (sub_pos.mpr ht_lt_one) ht_pos (by ring)
    have hcoef : (1 - t) + t = (1 : ℝ) := by ring
    have hsum :
        (1 - t) * f a + t * f b = f a := by
      calc
        (1 - t) * f a + t * f b
            = (1 - t) * f a + t * f a := by simpa [hb]
        _ = ((1 - t) + t) * f a := by ring
        _ = f a := by simpa [hcoef]
    simpa [x0, hsum, b] using hstrict'
  exact (lt_irrefl _ (lt_of_le_of_lt hx_ge hx_lt))

lemma fiberConvexSymm_of_strict (hQ : QFacHypotheses) [FiberStrictConvex] :
    FiberConvexSymm := by
  classical
  refine ⟨?_⟩
  intro x y z a hmin
  have hsymm :
      ∀ t : ℝ, CAlong x y z t = CAlong x y z (1 - t) :=
    fun t => CAlong_symm_half x y z t hQ
  have hstrict := FiberStrictConvex.strictConvex (x:=x) (y:=y) (z:=z)
  exact symmetric_strictConvex_localMin_eq_half hsymm hstrict hmin

/-- Main theorem (framework level): If q is stationary for C along its real-fiber,
    then Re(q) = 1/2. -/
 theorem stationary_implies_re_half
    (x y z a : ℝ) [FiberConvexSymm] :
    IsLocalMin (CAlong x y z) a → a = (1:ℝ)/2 := by
  intro hmin
  -- Use the class axiom strictlyConvex_stationary_at_half
  simpa using
    FiberConvexSymm.strictConvex_stationary_at_half (x:=x) (y:=y) (z:=z) (a:=a) hmin

/-- Convenience version: strict fiber convexity plus QFac hypotheses imply the stationary
    ⇒ `Re(q)=1/2` conclusion without manually instantiating `FiberConvexSymm`. -/
theorem stationary_implies_re_half_of_strict
    (x y z a : ℝ) (hQ : QFacHypotheses) [FiberStrictConvex] :
    IsLocalMin (CAlong x y z) a → a = (1 : ℝ) / 2 := by
  intro hmin
  haveI : FiberConvexSymm := fiberConvexSymm_of_strict hQ
  exact stationary_implies_re_half (x:=x) (y:=y) (z:=z) (a:=a) hmin

end

end QRH
