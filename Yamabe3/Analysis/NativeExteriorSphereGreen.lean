import Yamabe3.Analysis.NativeGaussSphereBoundaryFlux
import Yamabe3.Analysis.SphereBoundaryCutoff
import Yamabe3.Analysis.NativeRadialLaplacian
import PoincareLib.Geometry.Riemannian.Measure.Green.CompactSupport
import PoincareLib.Geometry.Riemannian.ScalarOperators.Product

/-!
# The actual exterior-sphere Green formula

The compact-test Green identity is applied to the literal smooth cutoff
times the literal lifting. The actual native gradient of this cutoff is
computed by the retained Gauss radial identity. Native-volume dominated
convergence and the already proved same-metric thin-layer limit then give
the boundary term in the actual induced sphere measure, with the exterior
domain's negative radial sign.

This theorem is for a genuine smooth representative and a genuine compact
smooth test. Passing it to an arbitrary completed canonical inverse still
requires representative regularity and the appropriate energy pairing.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff Bundle

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace Yamabe3.Analysis.EuclideanSphereTrace

open SphereBoundaryLayer GreenParametrix GreenMass.NativeGaussSphereArea

theorem native_exterior_cutoff_gradient_pairing
    (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E, g.inner x x v = inner ℝ x v)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (f : E → ℝ) (x : E) :
    g.inner x (g.leviCivitaData.gradient (exteriorSphereCutoff r ε) x)
      (g.leviCivitaData.gradient f x) =
      deriv (exteriorLayerProfile r ε) ‖x‖ * fderiv ℝ f x (‖x‖⁻¹ • x) := by
  let D := g.leviCivitaData
  by_cases hx : x = 0
  · subst x
    have hz : exteriorSphereCutoff r ε =ᶠ[𝓝 (0 : E)] 0 := by
      filter_upwards [ball_mem_nhds (0 : E) hr] with y hy
      have hyn : ‖y‖ < r := by simpa only [mem_ball, dist_zero_right] using hy
      exact exteriorLayerProfile_eq_zero hε hyn.le
    have hgrad : D.gradient (exteriorSphereCutoff r ε) 0 = 0 :=
      D.gradient_eq_zero_of_notMem_tsupport (notMem_tsupport_iff_eventuallyEq.mpr hz)
    change g.inner 0 (D.gradient (exteriorSphereCutoff r ε) 0) (D.gradient f 0) = _
    rw [hgrad, map_zero, zero_apply, smul_zero, map_zero, mul_zero]
  · have hscalar : g.inner x (D.gradient f x) x = fderiv ℝ f x x := by
      rw [D.inner_gradient]
      simp +instances only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
      rfl
    change g.inner x (D.gradient (fun y : E => exteriorLayerProfile r ε ‖y‖) x)
      (D.gradient f x) = _
    rw [native_gradient_radial g hGauss (exteriorLayerProfile r ε)
      (exteriorLayerProfile_smooth r ε).contDiffOn hx,
      map_smul, smul_apply, smul_eq_mul, g.symm x x (D.gradient f x), hscalar,
      map_smul, smul_eq_mul]
    ring

/-- The actual compact-test identity on the exterior of the closed ball.
The same native volume and actual induced sphere metric occur on the two
sides; the negative sign is derived from the outward-increasing cutoff. -/
theorem integral_native_exterior_sphere_green
    (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E, g.inner x x v = inner ℝ x v)
    {r : ℝ} (hr : 0 < r) {f ψ : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
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
    D.integrable_mul_laplacian hψ.contMDiff hf.contMDiff hψc
  have hGI : Integrable G g.volumeMeasure :=
    D.integrable_inner_gradient hψ.contMDiff hf.contMDiff hψc
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
      (hψ.continuous.mul (D.continuous_inner_gradient hχ.contMDiff hf.contMDiff)).integrable_of_hasCompactSupport
        hψc.mul_right
    have hprod (x : E) :
        g.inner x (D.gradient (fun y => χ y * ψ y) x) (D.gradient f x) =
          χ x * G x + Q x := by
      rw [D.gradient_mul (hχ.contMDiff.mdifferentiable (by simp) x)
        (hψ.contMDiff.mdifferentiable (by simp) x)]
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, G, Q]
    have hgreen : (∫ x, χ x * L x ∂g.volumeMeasure) =
        -((∫ x, χ x * G x ∂g.volumeMeasure) + ∫ x, Q x ∂g.volumeMeasure) := by
      calc
        _ = ∫ x, (χ x * ψ x) * D.laplacian f x ∂g.volumeMeasure := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by dsimp only [L]; ring
        _ = -(∫ x, g.inner x (D.gradient (fun y => χ y * ψ y) x) (D.gradient f x)
            ∂g.volumeMeasure) :=
          D.integral_mul_laplacian (hχ.contMDiff.mul hψ.contMDiff) hf.contMDiff hψc.mul_left
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
    ((contDiff_infty_iff_fderiv.mp hf).2.continuous) hψ.continuous).neg
  have hright' : Tendsto (fun ε : ℝ => ∫ x, exteriorSphereCutoff r ε x * A x ∂g.volumeMeasure)
      (𝓝[>] 0) (𝓝 (-(∫ θ : S, ψ (r • (θ : E)) * fderiv ℝ f (r • (θ : E)) (θ : E)
        ∂(gaussRadiusMetric g r hr.ne').volumeMeasure))) := by
    apply hright.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hexact ε hε).symm
  exact tendsto_nhds_unique hleft hright'

#print axioms native_exterior_cutoff_gradient_pairing
#print axioms integral_native_exterior_sphere_green

end Yamabe3.Analysis.EuclideanSphereTrace
