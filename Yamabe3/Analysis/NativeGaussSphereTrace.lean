import GreenMass.NativeGaussSphereArea
import Yamabe3.Analysis.EuclideanNormalTrace

/-!
# Simultaneous physical traces for the actual Gauss sphere metric

Both traces use the same actual function and the volume measure of the
metric induced by radius dilation into the supplied ambient metric. The
proved area identity, rather than a free geometric measure comparison,
transfers the Euclidean estimates. The density constant may be chosen before
the radius and function on each fixed compact coordinate ball.

The derivative here is the genuine radial directional derivative. Relating
it to a weak conormal functional still requires the Green formula and the
appropriate regularity of that same weak solution.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Bundle ENNReal

namespace Yamabe3.Analysis.EuclideanSphereTrace

open GreenMass.NativeGaussSphereArea

theorem exists_uniform_sphere_volume_density_bound
    (g : RiemannianMetric 3 E) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ R → ∀ θ : S,
      g.pullbackVolumeDensity id (r • (θ : E)) ≤ C := by
  have hρ : Continuous (g.pullbackVolumeDensity id) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (g.contDiffAt_pullbackVolumeDensity contMDiffAt_id
      (by rw [mfderiv_id]; exact Function.injective_id)).1.continuousAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
    hρ.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro r hr hrR θ
  have hx : r • (θ : E) ∈ closedBall (0 : E) R := by
    rw [mem_closedBall, dist_zero_right, norm_sphereTrace_radial θ hr.le]
    exact hrR
  have hCx : |g.pullbackVolumeDensity id (r • (θ : E))| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC _ hx
  exact (le_abs_self _).trans (hCx.trans (le_max_left _ _))

/-- Domination of actual native sphere integrals follows from the proved
same-metric area formula and an explicit ambient density upper bound. -/
theorem integral_gaussRadiusMetric_le_density_bound
    (g : RiemannianMetric 3 E) {r C : ℝ} (hr : r ≠ 0) (hC : 0 ≤ C)
    (hGauss : ∀ (θ : S) (w : E), g.inner (r • (θ : E)) (r • (θ : E)) w =
      inner ℝ (r • (θ : E)) w)
    (hρ : ∀ θ : S, g.pullbackVolumeDensity id (r • (θ : E)) ≤ C)
    {F : S → ℝ} (hF : ∀ θ, 0 ≤ F θ)
    (hFI : Integrable F (ENNReal.ofReal (r ^ 2) • angularVolume)) :
    (∫ θ, F θ ∂(gaussRadiusMetric g r hr).volumeMeasure) ≤
      C * ∫ θ, F θ ∂(ENNReal.ofReal (r ^ 2) • angularVolume) := by
  have hmeasure : (gaussRadiusMetric g r hr).volumeMeasure ≤
      ENNReal.ofReal C • (ENNReal.ofReal (r ^ 2) • angularVolume) := by
    rw [gaussRadiusMetric_volume_eq_weighted_polarArea g r hr hGauss]
    calc
      _ ≤ (ENNReal.ofReal (r ^ 2) • angularVolume).withDensity
          (fun _ : S => ENNReal.ofReal C) :=
        withDensity_mono (Eventually.of_forall fun θ => ENNReal.ofReal_le_ofReal (hρ θ))
      _ = _ := withDensity_const _
  have hi := integral_mono_measure hmeasure
    (Eventually.of_forall hF) (hFI.smul_measure ENNReal.ofReal_ne_top)
  simpa only [integral_smul_measure, ENNReal.toReal_ofReal hC, smul_eq_mul] using! hi

/-- Value and radial derivative traces of one actual function, using the
same induced geometric sphere measure. The density bound is explicit. -/
theorem integral_gaussRadiusMetric_cauchy_sq_le_scaled_energy
    (g : RiemannianMetric 3 E) {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hGauss : ∀ (θ : S) (w : E), g.inner (r • (θ : E)) (r • (θ : E)) w =
      inner ℝ (r • (θ : E)) w)
    (hρ : ∀ θ : S, g.pullbackVolumeDensity id (r • (θ : E)) ≤ C)
    {O : Set E} (hO : IsOpen O)
    (hKO : sphereTraceAnnulus (r / 2) (3 * r / 2) ⊆ O)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) :
    ((∫ θ : S, f (r • (θ : E)) ^ 2
        ∂(gaussRadiusMetric g r hr.ne').volumeMeasure) ≤
      (8 * C / r) * ∫ x in sphereTraceAnnulus (r / 2) (3 * r / 2),
        f x ^ 2 + r ^ 2 * ‖fderiv ℝ f x‖ ^ 2) ∧
    ((∫ θ : S, (fderiv ℝ f (r • (θ : E)) (θ : E)) ^ 2
        ∂(gaussRadiusMetric g r hr.ne').volumeMeasure) ≤
      (24 * C / r) * ∫ x in sphereTraceAnnulus (r / 2) (3 * r / 2),
        ‖fderiv ℝ f x‖ ^ 2 + r ^ 2 * ‖fderiv ℝ (fderiv ℝ f) x‖ ^ 2) := by
  have hs (θ : S) : r • (θ : E) ∈ O :=
    hKO (radial_mem_sphereTraceAnnulus (by positivity)
      (show r ∈ Icc (r / 2) (3 * r / 2) by constructor <;> linarith only [hr]) θ)
  have hfc := continuous_restriction_to_sphere hO hf.continuousOn r hs
  have hDc := continuous_restriction_to_sphere hO
    (hf.fderiv_of_isOpen (m := ∞) hO (by simp)).continuousOn r hs
  have hnc : Continuous (fun θ : S => fderiv ℝ f (r • (θ : E)) (θ : E)) :=
    hDc.clm_apply continuous_subtype_val
  have hfi : Integrable (fun θ : S => f (r • (θ : E)) ^ 2) angularVolume := by
    simpa only [integrableOn_univ, Pi.pow_apply] using!
      (hfc.pow 2).continuousOn.integrableOn_compact
        (μ := angularVolume) (isCompact_univ : IsCompact (univ : Set S))
  have hni : Integrable (fun θ : S => (fderiv ℝ f (r • (θ : E)) (θ : E)) ^ 2)
      angularVolume := by
    simpa only [integrableOn_univ, Pi.pow_apply] using!
      (hnc.pow 2).continuousOn.integrableOn_compact
        (μ := angularVolume) (isCompact_univ : IsCompact (univ : Set S))
  constructor
  · have hfirst := integral_gaussRadiusMetric_le_density_bound g hr.ne' hC hGauss hρ
      (fun θ => sq_nonneg _) (hfi.smul_measure ENNReal.ofReal_ne_top)
    have hsecond := mul_le_mul_of_nonneg_left
      (integral_physical_sphere_restriction_sq_le_scaled_energy hr hO hKO hf) hC
    apply hfirst.trans
    convert hsecond using 1 <;> ring
  · have hfirst := integral_gaussRadiusMetric_le_density_bound g hr.ne' hC hGauss hρ
      (fun θ => sq_nonneg _) (hni.smul_measure ENNReal.ofReal_ne_top)
    have hsecond := mul_le_mul_of_nonneg_left
      (integral_physical_sphere_normal_sq_le_scaled_hessian_energy hr hO hKO hf) hC
    apply hfirst.trans
    convert hsecond using 1 <;> ring

/-- On a fixed coordinate ball, the geometric density constant is chosen
before every radius and every smooth function. -/
theorem exists_uniform_gaussRadiusMetric_cauchy_trace_bound
    (g : RiemannianMetric 3 E) (R : ℝ)
    (hGauss : ∀ x w : E, g.inner x x w = inner ℝ x w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ R →
      ∀ {O : Set E}, IsOpen O → sphereTraceAnnulus (r / 2) (3 * r / 2) ⊆ O →
      ∀ {f : E → ℝ}, ContDiffOn ℝ ∞ f O →
      ((∫ θ : S, f (r • (θ : E)) ^ 2
          ∂(gaussRadiusMetric g r hr.ne').volumeMeasure) ≤
        (8 * C / r) * ∫ x in sphereTraceAnnulus (r / 2) (3 * r / 2),
          f x ^ 2 + r ^ 2 * ‖fderiv ℝ f x‖ ^ 2) ∧
      ((∫ θ : S, (fderiv ℝ f (r • (θ : E)) (θ : E)) ^ 2
          ∂(gaussRadiusMetric g r hr.ne').volumeMeasure) ≤
        (24 * C / r) * ∫ x in sphereTraceAnnulus (r / 2) (3 * r / 2),
          ‖fderiv ℝ f x‖ ^ 2 + r ^ 2 * ‖fderiv ℝ (fderiv ℝ f) x‖ ^ 2) := by
  obtain ⟨C, hC, hρ⟩ := exists_uniform_sphere_volume_density_bound g R
  refine ⟨C, hC, ?_⟩
  intro r hr hrR O hO hKO f hf
  exact integral_gaussRadiusMetric_cauchy_sq_le_scaled_energy g hr hC
    (fun θ w => hGauss (r • (θ : E)) w) (hρ r hr hrR) hO hKO hf

#print axioms integral_gaussRadiusMetric_cauchy_sq_le_scaled_energy
#print axioms exists_uniform_gaussRadiusMetric_cauchy_trace_bound

end Yamabe3.Analysis.EuclideanSphereTrace
