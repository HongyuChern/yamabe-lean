import Yamabe3.Analysis.EuclideanSphereBoundaryFlux
import Yamabe3.Analysis.Green.NativeLocalParametrix
import GreenMass.NativeGaussSphereArea

/-!
# Actual native-volume thin layers and the same Gauss sphere flux

The volume and surface integrals belong to the same supplied Riemannian
metric. Their densities are identified by existing native volume and
Gauss sphere area theorems. The limit uses the actual derivative of a fixed
smooth radial cutoff, the same function, and the same lifting. It supplies
the geometric boundary-layer limit required by a Green formula; it does
not identify a weak conormal without that additional argument.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff

namespace Yamabe3.Analysis.EuclideanSphereTrace

open SphereBoundaryLayer GreenParametrix GreenMass.NativeGaussSphereArea

/-- For an outward-increasing cutoff, the native thin-layer integral tends
to the positive radial flux on the same actual induced sphere metric. The
normal for the exterior of the ball is the negative of this direction. -/
theorem tendsto_native_gauss_radial_boundary_layer
    (g : RiemannianMetric 3 E) {r : ℝ} (hr : 0 < r)
    (hGauss : ∀ (θ : S) (w : E), g.inner (r • (θ : E)) (r • (θ : E)) w =
      inner ℝ (r • (θ : E)) w)
    {f ψ : E → ℝ} (hDf : Continuous (fderiv ℝ f)) (hψ : Continuous ψ) :
    Tendsto (fun ε : ℝ => ∫ x in sphereTraceAnnulus r (r + ε),
      deriv (exteriorLayerProfile r ε) ‖x‖ * ψ x *
        fderiv ℝ f x (‖x‖⁻¹ • x) ∂g.volumeMeasure)
      (𝓝[>] 0) (𝓝 (∫ θ : S, ψ (r • (θ : E)) *
        fderiv ℝ f (r • (θ : E)) (θ : E)
          ∂(gaussRadiusMetric g r hr.ne').volumeMeasure)) := by
  let ρ := g.pullbackVolumeDensity id
  let F : E → ℝ := fun x => ρ x * ψ x * fderiv ℝ f x x
  have hρ := native_density_smooth_positive g
  have hF : Continuous F :=
    (hρ.1.continuous.mul hψ).mul (hDf.clm_apply continuous_id)
  have hlim := tendsto_integral_radial_layer hr hF
  have hspace (ε : ℝ) :
      (∫ x in sphereTraceAnnulus r (r + ε),
        deriv (exteriorLayerProfile r ε) ‖x‖ * ψ x *
          fderiv ℝ f x (‖x‖⁻¹ • x) ∂g.volumeMeasure) =
      ∫ x in sphereTraceAnnulus r (r + ε),
        deriv (exteriorLayerProfile r ε) ‖x‖ * (F x / ‖x‖) := by
    have hK := (isCompact_sphereTraceAnnulus r (r + ε)).measurableSet
    rw [← integral_indicator hK, native_integral_eq_density g,
      ← integral_indicator hK]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    change (sphereTraceAnnulus r (r + ε)).indicator
      (fun x => deriv (exteriorLayerProfile r ε) ‖x‖ * ψ x *
        fderiv ℝ f x (‖x‖⁻¹ • x)) x * g.pullbackVolumeDensity id x =
      (sphereTraceAnnulus r (r + ε)).indicator
        (fun x => deriv (exteriorLayerProfile r ε) ‖x‖ * (F x / ‖x‖)) x
    by_cases hx : x ∈ sphereTraceAnnulus r (r + ε)
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      simp only [F, ρ, map_smul, smul_eq_mul, div_eq_mul_inv]
      ring
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
  have hboundary : r * (∫ θ : S, F (r • (θ : E)) ∂angularVolume) =
      ∫ θ : S, ψ (r • (θ : E)) * fderiv ℝ f (r • (θ : E)) (θ : E)
        ∂(gaussRadiusMetric g r hr.ne').volumeMeasure := by
    have hm : Continuous (fun θ : S => r • (θ : E)) := by
      simpa only [Pi.smul_apply] using!
        ((continuous_const : Continuous (fun _ : S => r)).smul
          (continuous_subtype_val : Continuous (Subtype.val : S → E)))
    have hρs : Continuous (fun θ : S => ρ (r • (θ : E))) := hρ.1.continuous.comp hm
    rw [gaussRadiusMetric_volume_eq_weighted_polarArea g r hr.ne' hGauss]
    change r * (∫ θ : S, F (r • (θ : E)) ∂angularVolume) =
      ∫ θ : S, ψ (r • (θ : E)) * fderiv ℝ f (r • (θ : E)) (θ : E)
        ∂(ENNReal.ofReal (r ^ 2) • angularVolume).withDensity
          (fun θ : S => ENNReal.ofReal (ρ (r • (θ : E))))
    have hmρ : Measurable (fun θ : S => ENNReal.ofReal (ρ (r • (θ : E)))) := by
      simpa only [Function.comp_def] using ENNReal.continuous_ofReal.measurable.comp hρs.measurable
    rw [integral_withDensity_eq_integral_toReal_smul hmρ
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hρ.2 _).le, smul_eq_mul,
      integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg r)]
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro θ
    simp only [F, ρ, map_smul, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (hρ.2 (r • (θ : E))).le]
    ring
  rw [hboundary] at hlim
  exact hlim.congr (fun ε => (hspace ε).symm)

/-- The coefficient and sign for an exterior-domain Jacobian are retained
explicitly: the gradient coefficient is eight and its outward normal at
an inner boundary is negative radial. -/
theorem tendsto_native_gauss_exterior_boundary_layer
    (g : RiemannianMetric 3 E) {r : ℝ} (hr : 0 < r)
    (hGauss : ∀ (θ : S) (w : E), g.inner (r • (θ : E)) (r • (θ : E)) w =
      inner ℝ (r • (θ : E)) w)
    {f ψ : E → ℝ} (hDf : Continuous (fderiv ℝ f)) (hψ : Continuous ψ) :
    Tendsto (fun ε : ℝ => -8 * (∫ x in sphereTraceAnnulus r (r + ε),
      deriv (exteriorLayerProfile r ε) ‖x‖ * ψ x *
        fderiv ℝ f x (‖x‖⁻¹ • x) ∂g.volumeMeasure))
      (𝓝[>] 0) (𝓝 (-8 * (∫ θ : S, ψ (r • (θ : E)) *
        fderiv ℝ f (r • (θ : E)) (θ : E)
          ∂(gaussRadiusMetric g r hr.ne').volumeMeasure))) :=
  (tendsto_native_gauss_radial_boundary_layer g hr hGauss hDf hψ).const_mul (-8)

#print axioms tendsto_native_gauss_radial_boundary_layer
#print axioms tendsto_native_gauss_exterior_boundary_layer

end Yamabe3.Analysis.EuclideanSphereTrace
