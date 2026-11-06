import Yamabe3.Analysis.NativeH4PoleGreen
import Yamabe3.Analysis.NativeManifoldC1Green

/-! Actual induced-area sphere Green formula for a C1 field with classical
C2 regularity off the pole and locally integrable density Laplacian. The
scaled H4 consumer proves these analytic premises from its graph data. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff Bundle
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
namespace Yamabe3.Analysis.EuclideanSphereTrace
open UniformElliptic SpherePolar SphereBoundaryLayer GreenParametrix GreenMass.NativeGaussSphereArea

theorem nativeC1OffZero_mul_laplacian_integrable
    (g:RiemannianMetric 3 E) (u:nativeC2OffZero)
    (hl:LocallyIntegrable (fun x=>g.pullbackVolumeDensity id x*g.leviCivitaData.laplacian u.val x) volume)
    {φ:E→ℝ} (hφ:Continuous φ) (hc:HasCompactSupport φ) :
    Integrable (fun x=>φ x*g.leviCivitaData.laplacian u.val x) g.volumeMeasure := by
  apply (native_integrable_iff_density g _).mpr
  apply (hl.integrable_smul_left_of_hasCompactSupport hφ hc).congr
  exact Eventually.of_forall fun x=>by simp only [smul_eq_mul];ring

theorem nativeC1OffZero_compact_green
    (g:RiemannianMetric 3 E) (u:nativeC2OffZero) (hf:ContDiff ℝ 1 u.val)
    (hl:LocallyIntegrable (fun x=>g.pullbackVolumeDensity id x*g.leviCivitaData.laplacian u.val x) volume)
    {φ:E→ℝ} (hφ:ContDiff ℝ 1 φ) (hc:HasCompactSupport φ) :
    (∫x,φ x*g.leviCivitaData.laplacian u.val x ∂g.volumeMeasure)=
    -(∫x,g.inner x (g.leviCivitaData.gradient φ x) (g.leviCivitaData.gradient u.val x) ∂g.volumeMeasure) := by
  apply integral_native_mul_laplacian_off_countable g hf (countable_singleton (0:E))
    (fun x hx=>u.property.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx)) hφ hc
  exact (native_integrable_iff_density g _).mp (nativeC1OffZero_mul_laplacian_integrable g u hl hφ.continuous hc)

theorem nativeC1OffZero_exterior_sphere_green
    (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E, g.inner x x v = inner ℝ x v)
    (u:nativeC2OffZero) (hf:ContDiff ℝ 1 u.val)
    (hl:LocallyIntegrable (fun x=>g.pullbackVolumeDensity id x*g.leviCivitaData.laplacian u.val x) volume)
    {r : ℝ} (hr : 0 < r) {ψ : E → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    (∫ x in {y : E | r < ‖y‖}, ψ x * g.leviCivitaData.laplacian u.val x +
      g.inner x (g.leviCivitaData.gradient ψ x) (g.leviCivitaData.gradient u.val x)
        ∂g.volumeMeasure) =
      -(∫ θ : S, ψ (r • (θ : E)) * fderiv ℝ u.val (r • (θ : E)) (θ : E)
        ∂(gaussRadiusMetric g r hr.ne').volumeMeasure) := by
  let D := g.leviCivitaData
  let L : E → ℝ := fun x => ψ x * D.laplacian u.val x
  let G : E → ℝ := fun x => g.inner x (D.gradient ψ x) (D.gradient u.val x)
  let A : E → ℝ := fun x => L x + G x
  have hLI : Integrable L g.volumeMeasure :=
    nativeC1OffZero_mul_laplacian_integrable g u hl hψ.continuous hψc
  have hGI : Integrable G g.volumeMeasure :=
    NativeC1Green.integrable_inner_gradient_C1 D (hψ.of_le (by norm_num)).contMDiff hf.contMDiff hψc
  have hAI : Integrable A g.volumeMeasure := hLI.add hGI
  have hexact (ε : ℝ) (hε : 0 < ε) :
      (∫ x, exteriorSphereCutoff r ε x * A x ∂g.volumeMeasure) =
      -(∫ x in sphereTraceAnnulus r (r + ε),
        deriv (exteriorLayerProfile r ε) ‖x‖ * ψ x *
          fderiv ℝ u.val x (‖x‖⁻¹ • x) ∂g.volumeMeasure) := by
    let χ := exteriorSphereCutoff r ε
    let Q : E → ℝ := fun x => ψ x * g.inner x (D.gradient χ x) (D.gradient u.val x)
    have hχ : ContDiff ℝ ∞ χ := exteriorSphereCutoff_smooth hr hε
    have hχb : ∀ᵐ x ∂g.volumeMeasure, ‖χ x‖ ≤ 1 := Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (exteriorSphereCutoff_nonneg r ε x)]
      exact exteriorSphereCutoff_le_one r ε x
    have hχL : Integrable (fun x => χ x * L x) g.volumeMeasure :=
      hLI.bdd_mul hχ.continuous.aestronglyMeasurable hχb
    have hχG : Integrable (fun x => χ x * G x) g.volumeMeasure :=
      hGI.bdd_mul hχ.continuous.aestronglyMeasurable hχb
    have hQI : Integrable Q g.volumeMeasure :=
      (hψ.continuous.mul (NativeC1Green.continuous_inner_gradient_C1 D ((hχ.of_le (by simp)).contMDiff) hf.contMDiff)).integrable_of_hasCompactSupport
        hψc.mul_right
    have hprod (x : E) :
        g.inner x (D.gradient (fun y => χ y * ψ y) x) (D.gradient u.val x) =
          χ x * G x + Q x := by
      rw [D.gradient_mul (hχ.contMDiff.mdifferentiable (by simp) x)
        (hψ.contMDiff.mdifferentiable (by norm_num) x)]
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, G, Q]
    have hgreen : (∫ x, χ x * L x ∂g.volumeMeasure) =
        -((∫ x, χ x * G x ∂g.volumeMeasure) + ∫ x, Q x ∂g.volumeMeasure) := by
      calc
        _ = ∫ x, (χ x * ψ x) * D.laplacian u.val x ∂g.volumeMeasure := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by dsimp only [L]; ring
        _ = -(∫ x, g.inner x (D.gradient (fun y => χ y * ψ y) x) (D.gradient u.val x)
            ∂g.volumeMeasure) :=
          nativeC1OffZero_compact_green g u hf hl ((hχ.of_le (by simp)).mul (hψ.of_le (by norm_num))) hψc.mul_left
        _ = _ := by
          simp_rw [hprod]
          rw [integral_add hχG hQI]
    have hQboundary : (∫ x, Q x ∂g.volumeMeasure) =
        ∫ x in sphereTraceAnnulus r (r + ε),
          deriv (exteriorLayerProfile r ε) ‖x‖ * ψ x *
            fderiv ℝ u.val x (‖x‖⁻¹ • x) ∂g.volumeMeasure := by
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
          change ψ x * g.inner x (D.gradient χ x) (D.gradient u.val x) = _
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
      (𝓝[>] 0) (𝓝 (-(∫ θ : S, ψ (r • (θ : E)) * fderiv ℝ u.val (r • (θ : E)) (θ : E)
        ∂(gaussRadiusMetric g r hr.ne').volumeMeasure))) := by
    apply hright.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hexact ε hε).symm
  exact tendsto_nhds_unique hleft hright'


theorem nativeC1OffZero_closedBall_sphere_green
    (g:RiemannianMetric 3 E) (hGauss:∀x v:E,g.inner x x v=inner ℝ x v)
    (u:nativeC2OffZero) (hf:ContDiff ℝ 1 u.val)
    (hl:LocallyIntegrable (fun x=>g.pullbackVolumeDensity id x*g.leviCivitaData.laplacian u.val x) volume)
    {r:ℝ} (hr:0<r) {ψ:E→ℝ} (hψ:ContDiff ℝ 2 ψ) (hc:HasCompactSupport ψ) :
    (∫x in closedBall (0:E) r,ψ x*g.leviCivitaData.laplacian u.val x+
      g.inner x (g.leviCivitaData.gradient ψ x) (g.leviCivitaData.gradient u.val x) ∂g.volumeMeasure)=
      ∫θ:S,ψ (r • (θ:E))*fderiv ℝ u.val (r • (θ:E)) (θ:E)
        ∂(gaussRadiusMetric g r hr.ne').volumeMeasure := by
  have hi:=nativeC1OffZero_mul_laplacian_integrable g u hl hψ.continuous hc
  have hg:=NativeC1Green.integrable_inner_gradient_C1 g.leviCivitaData (hψ.of_le (by norm_num)).contMDiff hf.contMDiff hc
  have htotal:=nativeC1OffZero_compact_green g u hf hl (hψ.of_le (by norm_num)) hc
  have hzero:(∫x,ψ x*g.leviCivitaData.laplacian u.val x+
      g.inner x (g.leviCivitaData.gradient ψ x) (g.leviCivitaData.gradient u.val x) ∂g.volumeMeasure)=0:=by
    rw [integral_add hi hg,htotal]
    ring
  have he:=nativeC1OffZero_exterior_sphere_green g hGauss u hf hl hr hψ hc
  have hs:=integral_add_compl (s:=closedBall (0:E) r) measurableSet_closedBall (hi.add hg)
  have hcompl:(closedBall (0:E) r)ᶜ={x:E|r<‖x‖}:=by
    ext x
    simp only [mem_compl_iff,mem_closedBall,dist_zero_right,not_le,mem_setOf_eq]
  simp only [Pi.add_apply] at hs
  rw [hcompl,he,hzero] at hs
  linarith only [hs]

#print axioms nativeC1OffZero_mul_laplacian_integrable
#print axioms nativeC1OffZero_compact_green
#print axioms nativeC1OffZero_exterior_sphere_green
#print axioms nativeC1OffZero_closedBall_sphere_green
end Yamabe3.Analysis.EuclideanSphereTrace
