import Yamabe3.Analysis.NativeEuclideanGreenC2

/-! Actual C2 exterior Green formula. Adapted proof from the retained
smooth native sphere formula, with C2 divergence/compact-test identity
proved in NativeEuclideanGreenC2. Induced metric area is unchanged. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff Bundle
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
namespace Yamabe3.Analysis.EuclideanSphereTrace
open SphereBoundaryLayer GreenParametrix GreenMass.NativeGaussSphereArea

theorem integral_native_exterior_sphere_green_C2
    (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E, g.inner x x v = inner ℝ x v)
    {r : ℝ} (hr : 0 < r) {f ψ : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    (∫ x in {y : E | r < ‖y‖}, ψ x * g.leviCivitaData.laplacian f x +
      g.inner x (g.leviCivitaData.gradient ψ x) (g.leviCivitaData.gradient f x)
        ∂g.volumeMeasure) =
      -(∫ θ : S, ψ (r • (θ : E)) * fderiv ℝ f (r • (θ : E)) (θ : E)
        ∂(gaussRadiusMetric g r hr.ne').volumeMeasure) := by
  let D := g.leviCivitaData
  let L : E → ℝ := fun x => ψ x * D.laplacian f x
  let G : E → ℝ := fun x => g.inner x (D.gradient ψ x) (D.gradient f x)
  let A : E → ℝ := fun x => L x + G x
  have hLI : Integrable L g.volumeMeasure :=
    (hψ.continuous.mul (continuous_native_laplacian_C2 g hf)).integrable_of_hasCompactSupport hψc.mul_right
  have hGI : Integrable G g.volumeMeasure :=
    integrable_native_inner_gradient_C2 g hψ hf hψc
  have hAI : Integrable A g.volumeMeasure := hLI.add hGI
  have hexact (ε : ℝ) (hε : 0 < ε) :
      (∫ x, exteriorSphereCutoff r ε x * A x ∂g.volumeMeasure) =
      -(∫ x in sphereTraceAnnulus r (r + ε),
        deriv (exteriorLayerProfile r ε) ‖x‖ * ψ x *
          fderiv ℝ f x (‖x‖⁻¹ • x) ∂g.volumeMeasure) := by
    let χ := exteriorSphereCutoff r ε
    let Q : E → ℝ := fun x => ψ x * g.inner x (D.gradient χ x) (D.gradient f x)
    have hχ : ContDiff ℝ ∞ χ := exteriorSphereCutoff_smooth hr hε
    have hχb : ∀ᵐ x ∂g.volumeMeasure, ‖χ x‖ ≤ 1 := Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (exteriorSphereCutoff_nonneg r ε x)]
      exact exteriorSphereCutoff_le_one r ε x
    have hχL : Integrable (fun x => χ x * L x) g.volumeMeasure :=
      hLI.bdd_mul hχ.continuous.aestronglyMeasurable hχb
    have hχG : Integrable (fun x => χ x * G x) g.volumeMeasure :=
      hGI.bdd_mul hχ.continuous.aestronglyMeasurable hχb
    have hQI : Integrable Q g.volumeMeasure :=
      (hψ.continuous.mul (continuous_native_inner_gradient_C2 g (hχ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hf)).integrable_of_hasCompactSupport
        hψc.mul_right
    have hprod (x : E) :
        g.inner x (D.gradient (fun y => χ y * ψ y) x) (D.gradient f x) =
          χ x * G x + Q x := by
      rw [D.gradient_mul (hχ.contMDiff.mdifferentiable (by simp) x)
        (hψ.contMDiff.mdifferentiable (by norm_num) x)]
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, G, Q]
    have hgreen : (∫ x, χ x * L x ∂g.volumeMeasure) =
        -((∫ x, χ x * G x ∂g.volumeMeasure) + ∫ x, Q x ∂g.volumeMeasure) := by
      calc
        _ = ∫ x, (χ x * ψ x) * D.laplacian f x ∂g.volumeMeasure := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by dsimp only [L]; ring
        _ = -(∫ x, g.inner x (D.gradient (fun y => χ y * ψ y) x) (D.gradient f x)
            ∂g.volumeMeasure) :=
          integral_native_mul_laplacian_C2 g ((hχ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).mul hψ) hf hψc.mul_left
        _ = _ := by
          simp_rw [hprod]
          rw [integral_add hχG hQI]
    have hQboundary : (∫ x, Q x ∂g.volumeMeasure) =
        ∫ x in sphereTraceAnnulus r (r + ε),
          deriv (exteriorLayerProfile r ε) ‖x‖ * ψ x *
            fderiv ℝ f x (‖x‖⁻¹ • x) ∂g.volumeMeasure := by
      calc
        _ = ∫ x in sphereTraceAnnulus r (r + ε), Q x ∂g.volumeMeasure := by
          symm
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro x hx
          have hn : ‖x‖ ∉ Ioo r (r + ε) := fun h => hx ⟨h.1.le, h.2.le⟩
          dsimp only [Q, χ]
          rw [native_exterior_cutoff_gradient_pairing g hGauss hr hε,
            exteriorLayerProfile_deriv_eq_zero_of_outside hε hn]
          ring
        _ = _ := by
          apply setIntegral_congr_fun (isCompact_sphereTraceAnnulus r (r + ε)).measurableSet
          intro x _
          change ψ x * g.inner x (D.gradient χ x) (D.gradient f x) = _
          rw [native_exterior_cutoff_gradient_pairing g hGauss hr hε]
          ring
    calc
      _ = (∫ x, χ x * L x ∂g.volumeMeasure) + ∫ x, χ x * G x ∂g.volumeMeasure := by
        rw [← integral_add hχL hχG]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by dsimp only [A, χ]; ring
      _ = -(∫ x, Q x ∂g.volumeMeasure) := by linarith only [hgreen]
      _ = _ := by rw [hQboundary]
  have hleft := tendsto_integral_exteriorSphereCutoff hr hAI
  have hright := (tendsto_native_gauss_radial_boundary_layer g hr
    (fun θ w => hGauss (r • (θ : E)) w)
    (hf.continuous_fderiv (by norm_num)) hψ.continuous).neg
  have hright' : Tendsto (fun ε : ℝ => ∫ x, exteriorSphereCutoff r ε x * A x ∂g.volumeMeasure)
      (𝓝[>] 0) (𝓝 (-(∫ θ : S, ψ (r • (θ : E)) * fderiv ℝ f (r • (θ : E)) (θ : E)
        ∂(gaussRadiusMetric g r hr.ne').volumeMeasure))) := by
    apply hright.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hexact ε hε).symm
  exact tendsto_nhds_unique hleft hright'


#print axioms integral_native_exterior_sphere_green_C2
end Yamabe3.Analysis.EuclideanSphereTrace
