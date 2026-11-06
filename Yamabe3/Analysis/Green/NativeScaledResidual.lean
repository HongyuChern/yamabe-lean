import Yamabe3.Analysis.Green.UniformRescaledResidual

/-!
# Uniform spatial C2 bounds for the actual rescaled parametrix forcing

The cutoff errors vanish on the actual inner cutoff ball. The smooth joint
scale extension of the density residual therefore controls the actual native
forcing, including its spatial derivatives, on a fixed rescaled annulus.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

open Set Metric Filter
open scoped ContDiff Topology Manifold

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT Yamabe3.Parametrix

theorem nativeResidual_eq_densityResidual_inner (g : RiemannianMetric 3 E)
    (χ : ContDiffBump (0 : E)) {x : E} (hx : ‖x‖ < χ.rIn) :
    nativeResidual g χ x = densityResidual (g.pullbackVolumeDensity id)
      (fun y => g.leviCivitaData.scalarCurvature y / 8) x := by
  have hχ : χ x = 1 := χ.one_of_mem_closedBall (by simpa using hx.le)
  simp only [nativeResidual, hχ, one_mul, singularCutoffError,
    native_laplacian_bump_zero_inner g χ hx, cutoffGradientCoefficient_zero_inner g χ hx,
    neg_zero, zero_mul, add_zero]

/-- One constant bounds the actual r²-rescaled native residual and both
spatial derivatives by C*r for every sufficiently small positive scale.
The sole density jet premise is exactly the one proved by the actual normal
chart construction; all coefficient regularity and bounds are constructed. -/
theorem exists_uniform_native_scaledResidual_C2_bound (g : RiemannianMetric 3 E)
    (hzero : fderiv ℝ (g.pullbackVolumeDensity id) 0 = 0)
    (χ : ContDiffBump (0 : E)) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r < R → ∀ z : E,
      (1 / 2 : ℝ) ≤ ‖z‖ → ‖z‖ ≤ 2 →
      ‖r ^ 2 * nativeResidual g χ (r • z)‖ ≤ C * r ∧
      ‖fderiv ℝ (fun x => r ^ 2 * nativeResidual g χ (r • x)) z‖ ≤ C * r ∧
      ‖fderiv ℝ (fderiv ℝ (fun x => r ^ 2 * nativeResidual g χ (r • x))) z‖ ≤ C * r := by
  let ρ : E → ℝ := g.pullbackVolumeDensity id
  let V : E → ℝ := fun y => g.leviCivitaData.scalarCurvature y / 8
  have hρ := native_density_smooth_positive g
  have hV : ContDiff ℝ ∞ V := g.leviCivitaData.contMDiff_scalarCurvature.contDiff.div_const 8
  obtain ⟨C, hC, hbound⟩ := exists_uniform_scaledDensityResidual_C2_bound hρ.1 hρ.2 hV
  let R : ℝ := min 1 (χ.rIn / 4)
  have hR : 0 < R := lt_min (by norm_num) (div_pos χ.rIn_pos (by norm_num))
  refine ⟨R, C, hR, hC, ?_⟩
  intro r hr hrR z hzlo hzup
  have hr1 : r ≤ 1 := (hrR.trans_le (min_le_left _ _)).le
  have hrχ : r < χ.rIn / 4 := hrR.trans_le (min_le_right _ _)
  have hz : z ≠ 0 := by intro heq; norm_num [heq] at hzlo
  have hnorm : ‖r • z‖ < χ.rIn := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  let f : E → ℝ := fun x => scaledDensityResidual ρ V (r, x)
  have heq : (fun x => r ^ 2 * nativeResidual g χ (r • x)) =ᶠ[𝓝 z] r • f := by
    have hncont : Continuous (fun x : E => ‖r • x‖) := (continuous_id.const_smul r).norm
    have hsmall : ∀ᶠ x in 𝓝 z, ‖r • x‖ < χ.rIn :=
      hncont.continuousAt.eventually (Iio_mem_nhds hnorm)
    filter_upwards [hsmall, eventually_ne_nhds hz] with x hx hx0
    change r ^ 2 * nativeResidual g χ (r • x) = r * scaledDensityResidual ρ V (r, x)
    rw [nativeResidual_eq_densityResidual_inner g χ hx,
      scaledDensityResidual_eq hρ.1 hρ.2 hzero hr hx0]
    ring
  have hb := hbound r ⟨hr.le, hr1⟩ z hzlo hzup
  have h1 : fderiv ℝ (r • f) = r • fderiv ℝ f := fderiv_const_smul_field r
  have h2 : fderiv ℝ (fderiv ℝ (r • f)) = r • fderiv ℝ (fderiv ℝ f) := by
    rw [h1]
    convert! fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ f) r
  refine ⟨?_, ?_, ?_⟩
  · have heqz : r ^ 2 * nativeResidual g χ (r • z) = r * f z := heq.self_of_nhds
    rw [heqz]
    change ‖r • f z‖ ≤ C * r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hb.1 hr.le).trans_eq (mul_comm r C)
  · rw [heq.fderiv_eq, h1]
    change ‖r • fderiv ℝ f z‖ ≤ C * r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hb.2.1 hr.le).trans_eq (mul_comm r C)
  · rw [heq.fderiv.fderiv_eq, h2]
    change ‖r • fderiv ℝ (fderiv ℝ f) z‖ ≤ C * r
    have hn2 : ‖r • fderiv ℝ (fderiv ℝ f) z‖ = r * ‖fderiv ℝ (fderiv ℝ f) z‖ := by
      convert! norm_smul_of_nonneg hr.le (fderiv ℝ (fderiv ℝ f) z)
    rw [hn2]
    exact (mul_le_mul_of_nonneg_left hb.2.2 hr.le).trans_eq (mul_comm r C)

#print axioms nativeResidual_eq_densityResidual_inner
#print axioms exists_uniform_native_scaledResidual_C2_bound

end Yamabe3.Analysis.GreenParametrix
