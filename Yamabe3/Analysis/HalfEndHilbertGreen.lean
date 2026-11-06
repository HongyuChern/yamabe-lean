import Yamabe3.Analysis.HalfEndEndpointTimeTesting
import Yamabe3.Analysis.HilbertIntegralExpansion

/-!
# Full time-dependent Hilbert Green tests on the half-line

The actual derivative curve is supplied with its proved one-sided
derivative identity.  Only positive-time scalar second derivatives are
required.  Absolute Parseval bounds justify the genuine half-line
integrals and the entrance terms, without pointwise spatial traces.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace Yamabe3.Analysis.Delaunay

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem halfEnd_deriv_inner_function {P : ℝ → H}
    (hP : Differentiable ℝ P) (x : H) (t : ℝ) :
    deriv (fun s => inner ℝ x (P s)) t = inner ℝ x (deriv P t) := by
  exact ((innerSL ℝ x).hasFDerivAt.comp_hasDerivAt t (hP t).hasDerivAt).deriv

/-- The same dominated Parseval summation holds for the actual restricted
Lebesgue measure, including a half-line with a finite entrance. -/
theorem hasSum_setIntegral_inner_coefficients [Countable ι]
    (b : HilbertBasis ι ℝ H) {P U : ℝ → H}
    (hP : Continuous P) (hc : HasCompactSupport P) (hU : Continuous U) (s : Set ℝ) :
    HasSum (fun i => ∫ t in s, inner ℝ (b i) (P t) * inner ℝ (b i) (U t))
      (∫ t in s, inner ℝ (P t) (U t)) := by
  let bound : ι → ℝ → ℝ := fun i t => |inner ℝ (b i) (P t)| * |inner ℝ (b i) (U t)|
  have hbi : IntegrableOn (fun t : ℝ => ∑' i, bound i t) s := by
    apply ((hP.norm.mul hU.norm).integrable_of_hasCompactSupport hc.norm.mul_right).integrableOn.mono'
    · apply Measurable.aestronglyMeasurable
      exact Measurable.tsum fun i =>
        (((innerSL ℝ (b i)).continuous.comp hP).abs.mul
          ((innerSL ℝ (b i)).continuous.comp hU).abs).measurable
    · apply Eventually.of_forall
      intro t
      rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun i => mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      exact (hilbert_absolute_pair_bound b (P t) (U t)).2
  apply hasSum_integral_of_dominated_convergence bound
  · intro i
    exact (((innerSL ℝ (b i)).continuous.comp hP).mul
      ((innerSL ℝ (b i)).continuous.comp hU)).aestronglyMeasurable
  · intro i
    exact Eventually.of_forall fun t => by simp only [bound, Real.norm_eq_abs, abs_mul, le_refl]
  · exact Eventually.of_forall fun t => (hilbert_absolute_pair_bound b (P t) (U t)).1
  · exact hbi
  · apply Eventually.of_forall
    intro t
    convert b.hasSum_inner_mul_inner (P t) (U t) using 1
    congr 1
    funext i
    rw [real_inner_comm (b i) (P t)]

private theorem halfEnd_hasSum_pair_coefficients (b : HilbertBasis ι ℝ H) (x y : H) :
    HasSum (fun i => inner ℝ (b i) x * inner ℝ (b i) y) (inner ℝ x y) := by
  convert b.hasSum_inner_mul_inner x y using 1
  congr 1
  funext i
  rw [real_inner_comm (b i) x]

/-- Green's identity with arbitrary compact smooth Hilbert-valued tests
and their actual spectral operator image.  Both nonzero Cauchy entrance
terms are retained.  The derivative at zero is the right derivative of
the same curve, rather than an independently specified boundary datum. -/
theorem halfEnd_hilbert_variable_green [Countable ι]
    (b : HilbertBasis ι ℝ H) (μ : ι → ℝ)
    {U DU F : ℝ → H} {V : ℝ → ℝ} {a₀ β : ℝ}
    (hU : Continuous U) (hDU : Continuous DU) (hF : Continuous F) (hV : Continuous V)
    (hD : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt U (DU t) (Ici 0) t)
    (hDD : ∀ i t, 0 < t →
      HasDerivAt (fun s => inner ℝ (b i) (DU s))
        (β * inner ℝ (b i) (DU t) + (μ i + a₀) * inner ℝ (b i) (U t) +
          inner ℝ (b i) (F t) - V t * inner ℝ (b i) (U t)) t)
    {P AP : ℝ → H} (hP : ContDiff ℝ ∞ P) (hcP : HasCompactSupport P)
    (hAP : Continuous AP)
    (hA : ∀ i t, inner ℝ (b i) (AP t) = μ i * inner ℝ (b i) (P t)) :
    (∫ t in Ioi (0 : ℝ), inner ℝ (deriv (deriv P) t) (U t)) +
      β * (∫ t in Ioi (0 : ℝ), inner ℝ (deriv P t) (U t)) -
      a₀ * (∫ t in Ioi (0 : ℝ), inner ℝ (P t) (U t)) +
      (∫ t in Ioi (0 : ℝ), inner ℝ (P t) (V t • U t)) -
      (∫ t in Ioi (0 : ℝ), inner ℝ (AP t) (U t)) =
      (∫ t in Ioi (0 : ℝ), inner ℝ (P t) (F t)) +
        inner ℝ (P 0) (DU 0) - inner ℝ (deriv P 0) (U 0) - β * inner ℝ (P 0) (U 0) := by
  have hzero (t : ℝ) (hp : P t = 0) : AP t = 0 := by
    apply b.repr.injective
    ext i
    rw [b.repr_apply_apply, hA, hp, inner_zero_right, mul_zero, map_zero]
    rfl
  have hcAP : HasCompactSupport AP := hcP.mono' (fun t ht =>
    subset_tsupport P (fun hp => ht (hzero t hp)))
  have hdP := (contDiff_infty_iff_deriv.mp hP).2
  have hddP := (contDiff_infty_iff_deriv.mp hdP).2
  have hco (i : ι) : ContDiff ℝ ∞ (fun t => inner ℝ (b i) (P t)) :=
    (innerSL ℝ (b i)).contDiff.comp hP
  have hcc (i : ι) : HasCompactSupport (fun t => inner ℝ (b i) (P t)) :=
    hcP.comp_left (map_zero (innerSL ℝ (b i)))
  have hdco (i : ι) : deriv (fun t => inner ℝ (b i) (P t)) =
      fun t => inner ℝ (b i) (deriv P t) :=
    funext fun t => halfEnd_deriv_inner_function (hP.differentiable (by simp)) (b i) t
  have hddco (i : ι) : deriv (deriv (fun t => inner ℝ (b i) (P t))) =
      fun t => inner ℝ (b i) (deriv (deriv P) t) := by
    rw [hdco]
    funext t
    exact halfEnd_deriv_inner_function (hdP.differentiable (by simp)) (b i) t
  have hscalar (i : ι) :
      (∫ t in Ioi (0 : ℝ), inner ℝ (b i) (deriv (deriv P) t) * inner ℝ (b i) (U t)) +
      β * (∫ t in Ioi (0 : ℝ), inner ℝ (b i) (deriv P t) * inner ℝ (b i) (U t)) -
      a₀ * (∫ t in Ioi (0 : ℝ), inner ℝ (b i) (P t) * inner ℝ (b i) (U t)) +
      (∫ t in Ioi (0 : ℝ), inner ℝ (b i) (P t) * inner ℝ (b i) (V t • U t)) -
      (∫ t in Ioi (0 : ℝ), inner ℝ (b i) (AP t) * inner ℝ (b i) (U t)) =
      (∫ t in Ioi (0 : ℝ), inner ℝ (b i) (P t) * inner ℝ (b i) (F t)) +
        inner ℝ (b i) (P 0) * inner ℝ (b i) (DU 0) -
        inner ℝ (b i) (deriv P 0) * inner ℝ (b i) (U 0) -
        β * (inner ℝ (b i) (P 0) * inner ℝ (b i) (U 0)) := by
    have h := halfEnd_second_order_endpoint_time_test (hco i) (hcc i)
      ((innerSL ℝ (b i)).continuous.comp hU) ((innerSL ℝ (b i)).continuous.comp hDU)
      hV ((innerSL ℝ (b i)).continuous.comp hF)
      (fun t ht => (innerSL ℝ (b i)).hasFDerivAt.comp_hasDerivWithinAt t (hD t ht))
      (hDD i)
    rw [hddco, hdco] at h
    simp only [Function.comp_apply, innerSL_apply_apply] at h
    have ha : (∫ t in Ioi (0 : ℝ), inner ℝ (b i) (AP t) * inner ℝ (b i) (U t)) =
        μ i * (∫ t in Ioi (0 : ℝ), inner ℝ (b i) (P t) * inner ℝ (b i) (U t)) := by
      simp_rw [hA, mul_assoc]
      rw [integral_const_mul]
    rw [ha]
    simp only [real_inner_smul_right, ← mul_assoc]
    linarith only [h]
  have s0 := hasSum_setIntegral_inner_coefficients b hP.continuous hcP hU (Ioi 0)
  have s1 := hasSum_setIntegral_inner_coefficients b hdP.continuous hcP.deriv hU (Ioi 0)
  have s2 := hasSum_setIntegral_inner_coefficients b hddP.continuous hcP.deriv.deriv hU (Ioi 0)
  have sA := hasSum_setIntegral_inner_coefficients b hAP hcAP hU (Ioi 0)
  have sF := hasSum_setIntegral_inner_coefficients b hP.continuous hcP hF (Ioi 0)
  have sV := hasSum_setIntegral_inner_coefficients b hP.continuous hcP (hV.smul hU) (Ioi 0)
  have s' := (((s2.add (HasSum.mul_left β s1)).sub (HasSum.mul_left a₀ s0)).add sV).sub sA
  have sRight := ((sF.add (halfEnd_hasSum_pair_coefficients b (P 0) (DU 0))).sub
      (halfEnd_hasSum_pair_coefficients b (deriv P 0) (U 0))).sub
      (HasSum.mul_left β (halfEnd_hasSum_pair_coefficients b (P 0) (U 0)))
  have hsR : HasSum (fun i =>
      (∫ t in Ioi (0 : ℝ), inner ℝ (b i) (P t) * inner ℝ (b i) (F t)) +
        inner ℝ (b i) (P 0) * inner ℝ (b i) (DU 0) -
        inner ℝ (b i) (deriv P 0) * inner ℝ (b i) (U 0) -
        β * (inner ℝ (b i) (P 0) * inner ℝ (b i) (U 0)))
      ((∫ t in Ioi (0 : ℝ), inner ℝ (deriv (deriv P) t) (U t)) +
        β * (∫ t in Ioi (0 : ℝ), inner ℝ (deriv P t) (U t)) -
        a₀ * (∫ t in Ioi (0 : ℝ), inner ℝ (P t) (U t)) +
        (∫ t in Ioi (0 : ℝ), inner ℝ (P t) (V t • U t)) -
        (∫ t in Ioi (0 : ℝ), inner ℝ (AP t) (U t))) := by
    convert s' using 1 <;> try rfl
    funext i
    exact (hscalar i).symm
  exact hsR.unique sRight

#print axioms hasSum_setIntegral_inner_coefficients
#print axioms halfEnd_hilbert_variable_green

end Yamabe3.Analysis.Delaunay
