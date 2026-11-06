import Yamabe3.Analysis.Green.RegularizedNewton
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Convergence of the cutoff error integrals

The derivative-of-cutoff terms have continuous, compactly supported
coefficients which vanish on a fixed inner ball. This module proves the
weighted convergence and integrable domination needed for those terms.
The hypotheses on the coefficient are explicit; native cutoff Laplacian and
gradient coefficients still need to be substituted using the product formula.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Yamabe3.RegularizedNewton

theorem radial_zero_power (x : E) (k : ℕ) :
    (‖x‖ ^ 2) ^ (-((k : ℝ) / 2)) = (‖x‖ ^ k)⁻¹ := by
  rw [← Real.rpow_natCast_mul (norm_nonneg x) 2 (-((k : ℝ) / 2))]
  norm_num only [Nat.cast_ofNat]
  have he : (2 : ℝ) * (-((k : ℝ) / 2)) = -(k : ℝ) := by ring
  rw [he, Real.rpow_neg (norm_nonneg x), Real.rpow_natCast]

theorem tendsto_radial_power {x : E} (hx : x ≠ 0) (k : ℕ) :
    Tendsto (fun ε : ℝ => (‖x‖ ^ 2 + ε ^ 2) ^ (-((k : ℝ) / 2)))
      (𝓝 0) (𝓝 ((‖x‖ ^ k)⁻¹)) := by
  have hc : Continuous (fun ε : ℝ => ‖x‖ ^ 2 + ε ^ 2) := by fun_prop
  have hb : Tendsto (fun ε : ℝ => ‖x‖ ^ 2 + ε ^ 2) (𝓝 0) (𝓝 (‖x‖ ^ 2)) := by
    simpa using hc.tendsto (0 : ℝ)
  have hp : (‖x‖ ^ 2) ^ (-((k : ℝ) / 2)) = (‖x‖ ^ k)⁻¹ := by
    exact radial_zero_power x k
  simpa only [hp] using hb.rpow_const (p := -((k : ℝ) / 2))
    (Or.inl (sq_pos_of_pos (norm_pos_iff.mpr hx)).ne')

theorem annular_radial_power_bound {r : ℝ} (hr : 0 < r) {x : E}
    (hx : r ≤ ‖x‖) (ε : ℝ) (k : ℕ) :
    (‖x‖ ^ 2 + ε ^ 2) ^ (-((k : ℝ) / 2)) ≤ (r ^ k)⁻¹ := by
  have hn : 0 < ‖x‖ := hr.trans_le hx
  refine (radial_rpow_le_inv_pow ε hn k).trans ?_
  apply (inv_le_inv₀ (pow_pos hn k) (pow_pos hr k)).mpr
  exact pow_le_pow_left₀ hr.le hx k

theorem annular_coefficient_bound {h : E → ℝ} {r : ℝ} (hr : 0 < r)
    (hzero : ∀ x, ‖x‖ < r → h x = 0) (ε : ℝ) (k : ℕ) (x : E) :
    ‖h x * (‖x‖ ^ 2 + ε ^ 2) ^ (-((k : ℝ) / 2))‖ ≤ ‖h x‖ * (r ^ k)⁻¹ := by
  by_cases hx : ‖x‖ < r
  · simp [hzero x hx]
  · have hp : 0 ≤ (‖x‖ ^ 2 + ε ^ 2) ^ (-((k : ℝ) / 2)) := by positivity
    rw [norm_mul, Real.norm_of_nonneg hp]
    exact mul_le_mul_of_nonneg_left
      (annular_radial_power_bound hr (le_of_not_gt hx) ε k) (norm_nonneg _)

theorem integrable_annular_coefficient {h : E → ℝ}
    (hc : Continuous h) (hs : HasCompactSupport h) {r : ℝ} (hr : 0 < r)
    (hzero : ∀ x, ‖x‖ < r → h x = 0) (ε : ℝ) (k : ℕ) :
    Integrable (fun x : E => h x * (‖x‖ ^ 2 + ε ^ 2) ^ (-((k : ℝ) / 2))) := by
  apply ((hc.integrable_of_hasCompactSupport hs).norm.mul_const ((r ^ k)⁻¹)).mono'
  · exact (hc.measurable.mul
      (((continuous_norm.pow 2).measurable.add_const (ε ^ 2)).pow_const (-((k : ℝ) / 2)))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (annular_coefficient_bound hr hzero ε k)

theorem integrable_singular_annular_coefficient {h : E → ℝ}
    (hc : Continuous h) (hs : HasCompactSupport h) {r : ℝ} (hr : 0 < r)
    (hzero : ∀ x, ‖x‖ < r → h x = 0) (k : ℕ) :
    Integrable (fun x : E => h x * (‖x‖ ^ k)⁻¹) := by
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, radial_zero_power] using
    integrable_annular_coefficient hc hs hr hzero 0 k

/-- This directly handles the potential (`k=1`) and radial gradient
(`k=3`) factors appearing when the smooth cutoff is differentiated. -/
theorem tendsto_integral_annular_coefficient {h : E → ℝ}
    (hc : Continuous h) (hs : HasCompactSupport h) {r : ℝ} (hr : 0 < r)
    (hzero : ∀ x, ‖x‖ < r → h x = 0) (k : ℕ) :
    Tendsto (fun ε : ℝ => ∫ x : E, h x * (‖x‖ ^ 2 + ε ^ 2) ^ (-((k : ℝ) / 2)))
      (𝓝 0) (𝓝 (∫ x : E, h x * (‖x‖ ^ k)⁻¹)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x : E => ‖h x‖ * (r ^ k)⁻¹)
  · apply Filter.Eventually.of_forall
    intro ε
    apply Measurable.aestronglyMeasurable
    exact hc.measurable.mul
      (((continuous_norm.pow 2).measurable.add_const (ε ^ 2)).pow_const (-((k : ℝ) / 2)))
  · exact Filter.Eventually.of_forall fun ε =>
      Filter.Eventually.of_forall (annular_coefficient_bound hr hzero ε k)
  · exact (hc.integrable_of_hasCompactSupport hs).norm.mul_const _
  · apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x = 0
    · have hh : h x = 0 := hzero x (by simpa [hx] using hr)
      simp only [hh, zero_mul]
      exact tendsto_const_nhds
    · exact tendsto_const_nhds.mul (tendsto_radial_power hx k)

theorem fderiv_bump_zero_on_inner (χ : ContDiffBump (0 : E)) {x : E}
    (hx : ‖x‖ < χ.rIn) : fderiv ℝ χ x = 0 := by
  have heq := χ.eventuallyEq_one_of_mem_ball (by simpa using hx)
  simpa using heq.fderiv_eq (𝕜 := ℝ)

/-- Apply the annular convergence theorem to an actual differentiated bump.
The multiplier can include the native density and pulled-back smooth test,
and the vector field can be the actual metric dual of the radial covector. -/
theorem tendsto_integral_bump_derivative (χ : ContDiffBump (0 : E))
    {m : E → ℝ} (hm : Continuous m) {A : E → E} (hA : Continuous A) :
    Tendsto (fun ε : ℝ => ∫ x : E,
      (m x * fderiv ℝ χ x (A x)) * (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)))
      (𝓝 0) (𝓝 (∫ x : E, (m x * fderiv ℝ χ x (A x)) * (‖x‖ ^ 3)⁻¹)) := by
  have hd : Continuous (fderiv ℝ χ) := (χ.contDiff (n := 2)).continuous_fderiv (by norm_num)
  have hc : Continuous (fun x : E => m x * fderiv ℝ χ x (A x)) :=
    hm.mul (hd.clm_apply hA)
  have hs : HasCompactSupport (fun x : E => m x * fderiv ℝ χ x (A x)) := by
    apply HasCompactSupport.of_support_subset_isCompact χ.hasCompactSupport.isCompact
    intro x hx
    by_contra hxχ
    have hd0 := fderiv_of_notMem_tsupport ℝ hxχ
    exact hx (by simp [hd0])
  have hz : ∀ x : E, ‖x‖ < χ.rIn → m x * fderiv ℝ χ x (A x) = 0 := by
    intro x hx
    simp only [fderiv_bump_zero_on_inner χ hx, zero_apply, mul_zero]
  exact tendsto_integral_annular_coefficient hc hs χ.rIn_pos hz 3

end Yamabe3.RegularizedNewton
