import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# The actual smooth radial boundary layer and its normalized flux limit

The cutoff is the fixed native smooth transition evaluated at `(s-r)/ε`.
Its derivative is an actual normalized nonnegative kernel.  Exact change
of variables and dominated convergence prove that integration against the
derivative over the real transition interval tends to the boundary value.
This is the one-dimensional radial step needed for the geometric Green
formula; no normal flux or boundary identity is assumed as an input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Yamabe3.Analysis.SphereBoundaryLayer

def layerKernel (t : ℝ) : ℝ := deriv Real.smoothTransition t

def exteriorLayerProfile (r ε s : ℝ) : ℝ := Real.smoothTransition ((s - r) / ε)

theorem exteriorLayerProfile_smooth (r ε : ℝ) :
    ContDiff ℝ ∞ (exteriorLayerProfile r ε) := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  exact hs.comp ((contDiff_id.sub contDiff_const).div_const ε)

theorem continuous_exteriorLayerProfile_deriv (r ε : ℝ) :
    Continuous (deriv (exteriorLayerProfile r ε)) :=
  ((exteriorLayerProfile_smooth r ε).deriv' (n := ∞)).continuous

theorem layerKernel_nonneg (t : ℝ) : 0 ≤ layerKernel t :=
  Real.smoothTransition.monotone.deriv_nonneg

theorem continuous_layerKernel : Continuous layerKernel := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  exact (hs.deriv' (n := ∞)).continuous

theorem integral_layerKernel : (∫ t in Icc (0 : ℝ) 1, layerKernel t) = 1 := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hd (t : ℝ) : HasDerivAt Real.smoothTransition (layerKernel t) t :=
    (hs.differentiable (by simp) t).hasDerivAt
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0 : ℝ) 1) => hd t)
    (continuous_layerKernel.intervalIntegrable 0 1)
  simpa only [Real.smoothTransition.one, Real.smoothTransition.zero, sub_zero] using hi

theorem exteriorLayerProfile_deriv (r ε s : ℝ) :
    deriv (exteriorLayerProfile r ε) s = layerKernel ((s - r) / ε) / ε := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have ha : HasDerivAt (fun t : ℝ => (t - r) / ε) (1 / ε) s := by
    simpa only [sub_zero, id_eq] using! ((hasDerivAt_id s).sub_const r).div_const ε
  have h := (hs.differentiable (by simp) ((s - r) / ε)).hasDerivAt.comp s ha
  simpa only [exteriorLayerProfile, layerKernel, Function.comp_def, mul_one_div] using! h.deriv

/-- Exact substitution in the genuine transition interval. -/
theorem integral_layer_derivative_rescale (r : ℝ) {ε : ℝ} (hε : 0 < ε)
    (F : ℝ → ℝ) :
    (∫ s in Icc r (r + ε), deriv (exteriorLayerProfile r ε) s * F s) =
      ∫ t in Icc (0 : ℝ) 1, layerKernel t * F (r + ε * t) := by
  simp only [exteriorLayerProfile_deriv]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : r ≤ r + ε),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  let G : ℝ → ℝ := fun s => layerKernel ((s - r) / ε) * F s
  have heq : (fun s => layerKernel ((s - r) / ε) / ε * F s) = fun s => ε⁻¹ * G s := by
    funext s
    dsimp only [G]
    ring
  rw [heq, intervalIntegral.integral_const_mul]
  have hsub := intervalIntegral.integral_comp_add_mul (a := (0 : ℝ)) (b := 1) G hε.ne' r
  simp only [mul_zero, add_zero, mul_one, smul_eq_mul] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro t _
  change layerKernel (((r + ε * t) - r) / ε) * F (r + ε * t) = _
  rw [show ((r + ε * t) - r) / ε = t by field_simp [hε.ne']; ring]

theorem tendsto_rescaled_layer_integral (r : ℝ) {F : ℝ → ℝ} (hF : Continuous F) :
    Tendsto (fun ε : ℝ => ∫ t in Icc (0 : ℝ) 1,
      layerKernel t * F (r + ε * t)) (𝓝 0) (𝓝 (F r)) := by
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact (Icc (r - 1) (r + 1))).exists_bound_of_continuousOn
    hF.continuousOn
  let C := max A 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound : ∀ᶠ ε : ℝ in 𝓝 0, ∀ᵐ t : ℝ ∂volume.restrict (Icc (0 : ℝ) 1),
      ‖layerKernel t * F (r + ε * t)‖ ≤ ‖layerKernel t‖ * C := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with ε hε
    have hεabs : |ε| < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hε
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have htAbs : |t| ≤ 1 := abs_le.mpr ⟨by linarith only [ht.1], ht.2⟩
    have hp : |ε * t| ≤ 1 := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul hεabs.le htAbs (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ 1)
    have hx : r + ε * t ∈ Icc (r - 1) (r + 1) := by
      have hh := abs_le.mp hp
      constructor <;> linarith only [hh.1, hh.2]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((hA _ hx).trans (le_max_left A 0)) (norm_nonneg _)
  have hlim : Tendsto (fun ε : ℝ => ∫ t in Icc (0 : ℝ) 1,
      layerKernel t * F (r + ε * t)) (𝓝 0)
      (𝓝 (∫ t in Icc (0 : ℝ) 1, layerKernel t * F r)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖layerKernel t‖ * C)
    · exact Eventually.of_forall fun ε =>
        (continuous_layerKernel.mul (hF.comp (continuous_const.add
          (continuous_const.mul continuous_id)))).aestronglyMeasurable
    · exact hbound
    · exact (continuous_layerKernel.norm.mul continuous_const).continuousOn.integrableOn_compact
        isCompact_Icc
    · apply Eventually.of_forall
      intro t
      have ht : Tendsto (fun ε : ℝ => r + ε * t) (𝓝 0) (𝓝 r) := by
        have hc : Continuous (fun ε : ℝ => r + ε * t) :=
          continuous_const.add (continuous_id.mul continuous_const)
        simpa only [ContinuousAt, zero_mul, add_zero] using hc.continuousAt (x := (0 : ℝ))
      exact (hF.continuousAt.tendsto.comp ht).const_mul (layerKernel t)
  have hv : (∫ t in Icc (0 : ℝ) 1, layerKernel t * F r) = F r := by
    rw [integral_mul_const, integral_layerKernel, one_mul]
  rwa [hv] at hlim

/-- The actual outward-increasing cutoff derivative converges to evaluation
at the same boundary radius. Restricting to positive thickness keeps the
real layer exactly `[r,r+ε]`. -/
theorem tendsto_integral_layer_derivative (r : ℝ) {F : ℝ → ℝ} (hF : Continuous F) :
    Tendsto (fun ε : ℝ => ∫ s in Icc r (r + ε),
      deriv (exteriorLayerProfile r ε) s * F s)
      (𝓝[>] 0) (𝓝 (F r)) := by
  apply ((tendsto_rescaled_layer_integral r hF).mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_layer_derivative_rescale r hε F).symm

#print axioms integral_layerKernel
#print axioms integral_layer_derivative_rescale
#print axioms tendsto_integral_layer_derivative

end Yamabe3.Analysis.SphereBoundaryLayer
