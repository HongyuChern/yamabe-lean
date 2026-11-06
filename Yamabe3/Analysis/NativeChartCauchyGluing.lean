import Yamabe3.Analysis.NativeChartExteriorCutoff
import Yamabe3.Analysis.NativeExteriorSphereGreen
import Yamabe3.Analysis.NativeChartSphereMetric
import Yamabe3.Analysis.Green.NativeChartOperatorTransfer
import PoincareLib.Geometry.Manifold.PartitionOfUnity.CompactSupport
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateEnergy

/-!
# W1: actual chart Green and smooth Cauchy gluing

The four pending proof units below retain their proof blocks verbatim.
Consolidation avoids repeated import initialization in the constrained
compiler environment. The three previous paths are compatibility imports.
The last theorem applies to the same two globally smooth fields and the
same original metric; it does not assert weak half-end regularity.
-/

-- Original proof unit: Yamabe3.Analysis.NativeChartBoundaryFlux
/-!
# Boundary layers for the actual original manifold chart

The gradient pairings are transported using the actual chart differential
and actual pullback coefficient identity. Compact extensions are constructed
from local germs solely to use the proved Euclidean thin-layer limit.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

open Set Filter MeasureTheory Metric PoincareMT VectorField
open scoped Topology Manifold ContDiff Bundle

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace Yamabe3.Analysis.EuclideanSphereTrace

open SphereBoundaryLayer PoincareMT.LeviCivitaData.Dirichlet
open GreenMass.NativeGaussSphereArea NativeChartSphereMetric GreenParametrix

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- The cutoff is constructed inside the given chart neighborhood. Its
product with the original local field preserves that field's germ on K. -/
private theorem exists_native_smooth_compact_extension_near_compact
    {O K : Set E} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u O) :
    ∃ v : E → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
      ∀ x ∈ K, v =ᶠ[𝓝 x] u := by
  obtain ⟨χ, hχ, hχc, hχO, _, hχone⟩ :=
    PoincareMT.exists_contMDiff_cutoff_of_isCompact (n := 3) hK hO hKO
  have hχd : ContDiff ℝ ∞ χ := hχ.contDiff
  refine ⟨fun x => χ x * u x, ?_, hχc.mul_right, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ O
    · exact hχd.contDiffAt.mul (hu.contDiffAt (hO.mem_nhds hx))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have hz := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hχO h))
      filter_upwards [hz] with y hy
      simp [hy]
  · intro x hx
    filter_upwards [hχone x hx] with y hy
    simpa only [Pi.one_apply, one_mul] using congrArg (fun a : ℝ => a * u y) hy

private theorem native_chart_gradient_pairing
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {x : E} (hx : x ∈ e.source)
    (hcoeff : gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    {f ψ : M → ℝ}
    (hf : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) f (e x))
    (hψ : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) ψ (e x)) :
    g.inner (e x) (g.leviCivitaData.gradient ψ (e x)) (g.leviCivitaData.gradient f (e x)) =
      gE.inner x (gE.leviCivitaData.gradient (ψ ∘ e) x)
        (gE.leviCivitaData.gradient (f ∘ e) x) := by
  have hD : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hinv : (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible := ⟨hD.mfderiv hx, rfl⟩
  have hm := ChartOperatorTransfer.metric_pairing_of_coefficients g gE e x hcoeff
  rw [gE.leviCivitaData.gradient_comp_eq_mpullback g.leviCivitaData
    (hD.mdifferentiableAt hx) hψ hinv hm,
    gE.leviCivitaData.gradient_comp_eq_mpullback g.leviCivitaData
      (hD.mdifferentiableAt hx) hf hinv hm, hm]
  simp only [mpullback, hinv.self_apply_inverse]

/-- The actual original-manifold cutoff pairing, in the same chart and
metric, is the literal radial directional derivative. -/
theorem chartExteriorCutoff_gradient_pairing
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hGauss : ∀ x v : E, gE.inner x x v = inner ℝ x v)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hs : closedBall (0 : E) (r + ε) ⊆ e.source)
    {x : E} (hx : x ∈ e.source)
    (hcoeff : gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    {f : M → ℝ} (hf : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) f (e x)) :
    g.inner (e x) (g.leviCivitaData.gradient (chartExteriorCutoff e r ε) (e x))
      (g.leviCivitaData.gradient f (e x)) =
      deriv (exteriorLayerProfile r ε) ‖x‖ * fderiv ℝ (f ∘ e) x (‖x‖⁻¹ • x) := by
  rw [native_chart_gradient_pairing g gE e he hei hx hcoeff hf
    ((chartExteriorCutoff_smooth e hei hr hε hs).mdifferentiable (by simp) (e x))]
  have hgerm : ((chartExteriorCutoff e r ε) ∘ e) =ᶠ[𝓝 x] exteriorSphereCutoff r ε := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact chartExteriorCutoff_comp_apply e r ε hy
  have hgrad : gE.leviCivitaData.gradient (((chartExteriorCutoff e r ε) ∘ e)) x =
      gE.leviCivitaData.gradient (exteriorSphereCutoff r ε) x := by
    unfold LeviCivitaData.gradient
    rw [Poincare.mvfderiv_eq_of_eventuallyEq hgerm]
  rw [hgrad]
  exact native_exterior_cutoff_gradient_pairing gE hGauss hr hε (f ∘ e) x

variable [MeasurableSpace M] [BorelSpace M]

/-- Exact finite-layer change of variables for the actual original metric. -/
theorem integral_chart_boundary_layer_eq_native
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hGauss : ∀ x v : E, gE.inner x x v = inner ℝ x v)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hs : closedBall (0 : E) (r + ε) ⊆ e.source)
    (hcoeff : ∀ x ∈ closedBall (0 : E) (r + ε),
      gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    {f ψ : M → ℝ} (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    (hψ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ψ) :
    (∫ y in e '' sphereTraceAnnulus r (r + ε), ψ y *
      g.inner y (g.leviCivitaData.gradient (chartExteriorCutoff e r ε) y)
        (g.leviCivitaData.gradient f y) ∂g.volumeMeasure) =
      ∫ x in sphereTraceAnnulus r (r + ε),
        deriv (exteriorLayerProfile r ε) ‖x‖ * ψ (e x) *
          fderiv ℝ (f ∘ e) x (‖x‖⁻¹ • x) ∂gE.volumeMeasure := by
  have hKb (x : E) (hx : x ∈ sphereTraceAnnulus r (r + ε)) :
      x ∈ closedBall (0 : E) (r + ε) := by
    simpa only [mem_closedBall, dist_zero_right] using hx.2
  have hK := isCompact_sphereTraceAnnulus r (r + ε)
  have hQ : Continuous (fun y : M => ψ y * g.inner y
      (g.leviCivitaData.gradient (chartExteriorCutoff e r ε) y)
      (g.leviCivitaData.gradient f y)) := hψ.continuous.mul
        (g.leviCivitaData.continuous_inner_gradient (chartExteriorCutoff_smooth e hei hr hε hs) hf)
  rw [integral_compact_image_eq_pullback_density (g := g) e he hei hK
    (fun x hx => hs (hKb x hx)) hQ.measurable]
  have hright : (∫ x in sphereTraceAnnulus r (r + ε),
      deriv (exteriorLayerProfile r ε) ‖x‖ * ψ (e x) *
        fderiv ℝ (f ∘ e) x (‖x‖⁻¹ • x) ∂gE.volumeMeasure) =
      ∫ x in sphereTraceAnnulus r (r + ε),
        (deriv (exteriorLayerProfile r ε) ‖x‖ * ψ (e x) *
          fderiv ℝ (f ∘ e) x (‖x‖⁻¹ • x)) * gE.pullbackVolumeDensity id x := by
    rw [← integral_indicator hK.measurableSet, native_integral_eq_density gE,
      ← integral_indicator hK.measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ sphereTraceAnnulus r (r + ε)
      · simp only [indicator_of_mem hx]
      · simp only [indicator_of_notMem hx, zero_mul]
  rw [hright]
  apply setIntegral_congr_fun hK.measurableSet
  intro x hx
  change ψ (e x) * g.inner (e x)
    (g.leviCivitaData.gradient (chartExteriorCutoff e r ε) (e x))
    (g.leviCivitaData.gradient f (e x)) * g.pullbackVolumeDensity e x =
      (deriv (exteriorLayerProfile r ε) ‖x‖ * ψ (e x) *
        fderiv ℝ (f ∘ e) x (‖x‖⁻¹ • x)) * gE.pullbackVolumeDensity id x
  rw [chartExteriorCutoff_gradient_pairing g gE e he hei hGauss hr hε hs
    (hs (hKb x hx)) (hcoeff x (hKb x hx)) (hf.mdifferentiable (by simp) (e x)),
    pullbackVolumeDensity_eq_of_coefficients g gE e x (hcoeff x (hKb x hx))]
  ring

/-- The original manifold's actual thin-layer gradient pairing converges
to its actual induced chart-sphere area pairing. All Euclidean extensions
are constructed from genuine local smooth germs inside the retained chart. -/
theorem tendsto_chart_radial_boundary_layer
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hGauss : ∀ x v : E, gE.inner x x v = inner ℝ x v)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hs : closedBall (0 : E) R ⊆ e.source)
    (hcoeff : ∀ x ∈ closedBall (0 : E) R,
      gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    (hSphere : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source)
    {f ψ : M → ℝ} (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    (hψ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ψ) :
    Tendsto (fun ε : ℝ => ∫ y in e '' sphereTraceAnnulus r (r + ε), ψ y *
      g.inner y (g.leviCivitaData.gradient (chartExteriorCutoff e r ε) y)
        (g.leviCivitaData.gradient f y) ∂g.volumeMeasure)
      (𝓝[>] 0) (𝓝 (∫ θ : S, ψ (e (r • (θ : E))) *
        fderiv ℝ (f ∘ e) (r • (θ : E)) (θ : E)
          ∂(chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure)) := by
  obtain ⟨F, hF, _, hFg⟩ := exists_native_smooth_compact_extension_near_compact
    e.open_source (isCompact_closedBall (0 : E) R) hs (hf.comp_contMDiffOn he).contDiffOn
  obtain ⟨Ψ, hΨ, _, hΨg⟩ := exists_native_smooth_compact_extension_near_compact
    e.open_source (isCompact_closedBall (0 : E) R) hs (hψ.comp_contMDiffOn he).contDiffOn
  have hsr (θ : S) : r • (θ : E) ∈ closedBall (0 : E) R := by
    have h := radial_mem_sphereTraceAnnulus hr ⟨le_rfl, hrR.le⟩ θ
    simpa only [mem_closedBall, dist_zero_right] using h.2
  have hlim := tendsto_native_gauss_radial_boundary_layer gE hr
    (fun θ w => hGauss (r • (θ : E)) w)
    ((contDiff_infty_iff_fderiv.mp hF).2.continuous) hΨ.continuous
  have hb : (∫ θ : S, Ψ (r • (θ : E)) * fderiv ℝ F (r • (θ : E)) (θ : E)
      ∂(gaussRadiusMetric gE r hr.ne').volumeMeasure) =
      ∫ θ : S, ψ (e (r • (θ : E))) * fderiv ℝ (f ∘ e) (r • (θ : E)) (θ : E)
        ∂(chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure := by
    rw [chartRadiusMetric_eq_gaussRadiusMetric g gE e he hei r hr.ne' hSphere
      (fun θ => hcoeff _ (hsr θ))]
    apply integral_congr_ae
    exact Eventually.of_forall fun θ => by
      change Ψ (r • (θ : E)) * fderiv ℝ F (r • (θ : E)) (θ : E) =
        ψ (e (r • (θ : E))) * fderiv ℝ (f ∘ e) (r • (θ : E)) (θ : E)
      rw [(hΨg _ (hsr θ)).self_of_nhds, (hFg _ (hsr θ)).fderiv_eq]
      rfl
  rw [hb] at hlim
  apply hlim.congr'
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < R - r :=
    (eventually_lt_nhds (sub_pos.mpr hrR)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hεR
  have hεle : r + ε ≤ R := by linarith only [hεR]
  have hbs : closedBall (0 : E) (r + ε) ⊆ closedBall (0 : E) R :=
    closedBall_subset_closedBall hεle
  rw [integral_chart_boundary_layer_eq_native g gE e he hei hGauss hr hε
    (hbs.trans hs) (fun x hx => hcoeff x (hbs hx)) hf hψ]
  apply setIntegral_congr_fun (isCompact_sphereTraceAnnulus r (r + ε)).measurableSet
  intro x hx
  have hxb : x ∈ closedBall (0 : E) R := by
    simpa only [mem_closedBall, dist_zero_right] using hx.2.trans hεle
  change deriv (exteriorLayerProfile r ε) ‖x‖ * Ψ x *
    fderiv ℝ F x (‖x‖⁻¹ • x) = _
  rw [(hΨg x hxb).self_of_nhds, (hFg x hxb).fderiv_eq]
  rfl

#print axioms chartExteriorCutoff_gradient_pairing
#print axioms integral_chart_boundary_layer_eq_native
#print axioms tendsto_chart_radial_boundary_layer

end Yamabe3.Analysis.EuclideanSphereTrace

end -- Close this original proof unit's noncomputable section.


-- Original proof unit: Yamabe3.Analysis.NativeChartExteriorGreen
/-!
# The original manifold's exterior chart-ball Green formula

The compact-test identity is applied on the original manifold to its actual
smooth exterior cutoff. Native volume dominated convergence and the proved
chart sphere flux give the real boundary term with negative radial orientation.
The sphere area is induced from the original metric through the actual chart.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff Bundle

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace Yamabe3.Analysis.EuclideanSphereTrace

open SphereBoundaryLayer PoincareMT.LeviCivitaData.Dirichlet NativeChartSphereMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [ConnectedSpace M]

private theorem chartExteriorCutoff_gradient_zero_outside
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    {r ε : ℝ} (hε : 0 < ε) (hs : closedBall (0 : E) (r + ε) ⊆ e.source)
    {y : M} (hy : y ∉ e '' closedBall (0 : E) (r + ε)) :
    g.leviCivitaData.gradient (chartExteriorCutoff e r ε) y = 0 := by
  have hsub : tsupport (coordinateExtension e (fun x => 1 - exteriorSphereCutoff r ε x)) ⊆
      e '' closedBall (0 : E) (r + ε) :=
    (tsupport_coordinateExtension_subset_image e (innerSphereCutoff_compactSupport hε)
      ((innerSphereCutoff_tsupport_subset hε).trans hs)).trans
        (image_mono (innerSphereCutoff_tsupport_subset hε))
  have hz := notMem_tsupport_iff_eventuallyEq.mp (fun ht => hy (hsub ht))
  have hχ : chartExteriorCutoff e r ε =ᶠ[𝓝 y] (fun _ : M => (1 : ℝ)) := by
    filter_upwards [hz] with z hz
    change 1 - coordinateExtension e (fun x => 1 - exteriorSphereCutoff r ε x) z = 1
    rw [hz, Pi.zero_apply, sub_zero]
  unfold LeviCivitaData.gradient
  rw [Poincare.mvfderiv_eq_of_eventuallyEq hχ]
  simp only [mvfderiv_const, map_zero]

private theorem integral_chart_cutoff_gradient_eq_layer
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hGauss : ∀ x v : E, gE.inner x x v = inner ℝ x v)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hs : closedBall (0 : E) (r + ε) ⊆ e.source)
    (hcoeff : ∀ x ∈ closedBall (0 : E) (r + ε),
      gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    {f ψ : M → ℝ} (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f) :
    (∫ y, ψ y * g.inner y (g.leviCivitaData.gradient (chartExteriorCutoff e r ε) y)
      (g.leviCivitaData.gradient f y) ∂g.volumeMeasure) =
      ∫ y in e '' sphereTraceAnnulus r (r + ε), ψ y *
        g.inner y (g.leviCivitaData.gradient (chartExteriorCutoff e r ε) y)
          (g.leviCivitaData.gradient f y) ∂g.volumeMeasure := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  by_cases hyb : y ∈ e '' closedBall (0 : E) (r + ε)
  · obtain ⟨x, hx, rfl⟩ := hyb
    have hn : ‖x‖ ∉ Ioo r (r + ε) := by
      intro hn
      exact hy ⟨x, ⟨hn.1.le, hn.2.le⟩, rfl⟩
    rw [chartExteriorCutoff_gradient_pairing g gE e he hei hGauss hr hε hs (hs hx)
      (hcoeff x hx) (hf.mdifferentiable (by simp) (e x)),
      exteriorLayerProfile_deriv_eq_zero_of_outside hε hn]
    ring
  · rw [chartExteriorCutoff_gradient_zero_outside g e hε hs hyb,
      map_zero, zero_apply, mul_zero]

/-- The actual boundary formula for the complement of a closed chart ball.
Its normal is the negative of the outward radial normal of that chart ball. -/
theorem integral_native_chart_exterior_green
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hGauss : ∀ x v : E, gE.inner x x v = inner ℝ x v)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hs : closedBall (0 : E) R ⊆ e.source)
    (hcoeff : ∀ x ∈ closedBall (0 : E) R,
      gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    (hSphere : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source)
    {f ψ : M → ℝ} (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    (hψ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ψ) (hψc : HasCompactSupport ψ) :
    (∫ y in (e '' closedBall (0 : E) r)ᶜ, ψ y * g.leviCivitaData.laplacian f y +
      g.inner y (g.leviCivitaData.gradient ψ y) (g.leviCivitaData.gradient f y)
        ∂g.volumeMeasure) =
      -(∫ θ : S, ψ (e (r • (θ : E))) * fderiv ℝ (f ∘ e) (r • (θ : E)) (θ : E)
        ∂(chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure) := by
  let D := g.leviCivitaData
  let L : M → ℝ := fun y => ψ y * g.leviCivitaData.laplacian f y
  let G : M → ℝ := fun y => g.inner y (g.leviCivitaData.gradient ψ y) (g.leviCivitaData.gradient f y)
  let A : M → ℝ := fun y => L y + G y
  have hLI : Integrable L g.volumeMeasure := g.leviCivitaData.integrable_mul_laplacian hψ hf hψc
  have hGI : Integrable G g.volumeMeasure := g.leviCivitaData.integrable_inner_gradient hψ hf hψc
  have hAI : Integrable A g.volumeMeasure := hLI.add hGI
  have hexact (ε : ℝ) (hε : 0 < ε) (hεR : r + ε ≤ R) :
      (∫ y, chartExteriorCutoff e r ε y * A y ∂g.volumeMeasure) =
      -(∫ y in e '' sphereTraceAnnulus r (r + ε), ψ y *
        g.inner y (g.leviCivitaData.gradient (chartExteriorCutoff e r ε) y) (g.leviCivitaData.gradient f y)
          ∂g.volumeMeasure) := by
    have hbs := closedBall_subset_closedBall (x := (0 : E)) hεR
    have hsε := hbs.trans hs
    let χ := chartExteriorCutoff e r ε
    let Q : M → ℝ := fun y => ψ y * g.inner y (g.leviCivitaData.gradient χ y) (g.leviCivitaData.gradient f y)
    have hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ := chartExteriorCutoff_smooth e hei hr hε hsε
    have hχb : ∀ᵐ y ∂g.volumeMeasure, ‖χ y‖ ≤ 1 := Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (chartExteriorCutoff_range e r ε y).1]
      exact (chartExteriorCutoff_range e r ε y).2
    have hχL : Integrable (fun y => χ y * L y) g.volumeMeasure :=
      hLI.bdd_mul hχ.continuous.aestronglyMeasurable hχb
    have hχG : Integrable (fun y => χ y * G y) g.volumeMeasure :=
      hGI.bdd_mul hχ.continuous.aestronglyMeasurable hχb
    have hQI : Integrable Q g.volumeMeasure :=
      (hψ.continuous.mul (g.leviCivitaData.continuous_inner_gradient hχ hf)).integrable_of_hasCompactSupport
        hψc.mul_right
    have hprod (y : M) :
        g.inner y (g.leviCivitaData.gradient (fun z => χ z * ψ z) y) (g.leviCivitaData.gradient f y) =
          χ y * G y + Q y := by
      rw [g.leviCivitaData.gradient_mul (hχ.mdifferentiable (by simp) y) (hψ.mdifferentiable (by simp) y)]
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, G, Q]
    have hgreen : (∫ y, χ y * L y ∂g.volumeMeasure) =
        -((∫ y, χ y * G y ∂g.volumeMeasure) + ∫ y, Q y ∂g.volumeMeasure) := by
      calc
        _ = ∫ y, (χ y * ψ y) * g.leviCivitaData.laplacian f y ∂g.volumeMeasure := by
          apply integral_congr_ae
          exact Eventually.of_forall fun y => by dsimp only [L]; ring
        _ = -(∫ y, g.inner y (g.leviCivitaData.gradient (fun z => χ z * ψ z) y) (g.leviCivitaData.gradient f y)
            ∂g.volumeMeasure) := g.leviCivitaData.integral_mul_laplacian (hχ.mul hψ) hf hψc.mul_left
        _ = _ := by
          simp_rw [hprod]
          rw [integral_add hχG hQI]
    calc
      _ = (∫ y, χ y * L y ∂g.volumeMeasure) + ∫ y, χ y * G y ∂g.volumeMeasure := by
        rw [← integral_add hχL hχG]
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by dsimp only [A, χ]; ring
      _ = -(∫ y, Q y ∂g.volumeMeasure) := by linarith only [hgreen]
      _ = _ := by
        congr 1
        exact integral_chart_cutoff_gradient_eq_layer g gE e he hei hGauss hr hε hsε
          (fun x hx => hcoeff x (hbs hx)) hf
  have hleft := tendsto_integral_chartExteriorCutoff e hei hr hrR hs hAI
  have hright := (tendsto_chart_radial_boundary_layer g gE e he hei hGauss hr hrR hs
    hcoeff hSphere hf hψ).neg
  have hright' : Tendsto (fun ε : ℝ => ∫ y, chartExteriorCutoff e r ε y * A y ∂g.volumeMeasure)
      (𝓝[>] 0) (𝓝 (-(∫ θ : S, ψ (e (r • (θ : E))) *
        fderiv ℝ (f ∘ e) (r • (θ : E)) (θ : E)
          ∂(chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure))) := by
    apply hright.congr'
    have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < R - r :=
      (eventually_lt_nhds (sub_pos.mpr hrR)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hεR
    exact (hexact ε hε (by linarith only [hεR])).symm
  exact tendsto_nhds_unique hleft hright'

#print axioms integral_native_chart_exterior_green

end Yamabe3.Analysis.EuclideanSphereTrace

end -- Close this original proof unit's noncomputable section.


-- Original proof unit: Yamabe3.Analysis.NativeChartExteriorTopology
/-!
# The actual chart sphere belongs to the closure of its exterior

Positive radial perturbations remain inside the retained chart and outside
the closed chart ball. Their images converge to the actual sphere point.
This supplies the closure membership needed by the local-representative
energy argument; it is not an assumption about an abstract boundary.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff

namespace Yamabe3.Analysis.EuclideanSphereTrace

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem chart_sphere_mem_closure_exterior
    (e : OpenPartialHomeomorph E M) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hs : closedBall (0 : E) R ⊆ e.source) (θ : S) :
    e (r • (θ : E)) ∈ closure (e '' closedBall (0 : E) r)ᶜ := by
  have hsr : closedBall (0 : E) r ⊆ e.source :=
    (closedBall_subset_closedBall hrR.le).trans hs
  have hx : r • (θ : E) ∈ e.source := by
    apply hsr
    rw [mem_closedBall, dist_zero_right, norm_sphereTrace_radial θ hr.le]
  have hc : Continuous (fun t : ℝ => (r + t) • (θ : E)) :=
    (continuous_const.add continuous_id).smul continuous_const
  have ht : Tendsto (fun t : ℝ => e ((r + t) • (θ : E))) (𝓝[>] 0)
      (𝓝 (e (r • (θ : E)))) := by
    have h := ((e.continuousOn.continuousAt (e.open_source.mem_nhds hx)).tendsto.comp
      (show Tendsto (fun t : ℝ => (r + t) • (θ : E)) (𝓝 0) (𝓝 (r • (θ : E))) by
        simpa only [add_zero] using hc.tendsto 0))
    exact h.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto ht
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < R - r :=
    (eventually_lt_nhds (sub_pos.mpr hrR)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht0 htR
  have hrt : 0 < r + t := add_pos hr ht0
  have hxt : (r + t) • (θ : E) ∈ e.source := by
    apply hs
    rw [mem_closedBall, dist_zero_right, norm_sphereTrace_radial θ hrt.le]
    linarith only [htR]
  rintro ⟨x, hxr, hxe⟩
  have heq : x = (r + t) • (θ : E) := e.injOn (hsr hxr) hxt hxe
  rw [heq, mem_closedBall, dist_zero_right, norm_sphereTrace_radial θ hrt.le] at hxr
  have htpos : 0 < t := ht0
  linarith only [htpos, hxr]

theorem measurableSet_chart_ball_exterior
    (e : OpenPartialHomeomorph E M) {r R : ℝ} (hrR : r ≤ R)
    (hs : closedBall (0 : E) R ⊆ e.source) :
    MeasurableSet (e '' closedBall (0 : E) r)ᶜ := by
  exact ((isCompact_closedBall (0 : E) r).image_of_continuousOn
    (e.continuousOn.mono ((closedBall_subset_closedBall hrR).trans hs))).measurableSet.compl

#print axioms chart_sphere_mem_closure_exterior
#print axioms measurableSet_chart_ball_exterior

end Yamabe3.Analysis.EuclideanSphereTrace

end -- Close this original proof unit's noncomputable section.


-- Original proof unit: Yamabe3.Analysis.NativeChartCauchyGluing
/-!
# The distributional interface term for actual smooth chart-ball fields

The two fields, their Laplacians, the volume measure, and the induced
boundary measure all belong to the same original metric. The exterior
normal is negative radial. The piecewise function is formed explicitly;
its distributional equation is proved from the native Green formula.

The regularity here is deliberately explicit: both fields have global
smooth representatives. This theorem does not identify the weak forced
half-end with such representatives or with a weak conormal.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option quotPrecheck false

open Set MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff Bundle

namespace Yamabe3.Analysis.EuclideanSphereTrace

open NativeChartSphereMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

private theorem native_gradient_integral_symm (g : RiemannianMetric 3 M)
    (A : Set M) (f h : M → ℝ) :
    (∫ x in A, g.inner x (g.leviCivitaData.gradient f x)
      (g.leviCivitaData.gradient h x) ∂g.volumeMeasure) =
    ∫ x in A, g.inner x (g.leviCivitaData.gradient h x)
      (g.leviCivitaData.gradient f x) ∂g.volumeMeasure := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change inner ℝ (g.leviCivitaData.gradient f x) (g.leviCivitaData.gradient h x) =
      inner ℝ (g.leviCivitaData.gradient h x) (g.leviCivitaData.gradient f x)
    exact real_inner_comm _ _

section Boundary

variable (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
  (e : OpenPartialHomeomorph E M)
  (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
  (hGauss : ∀ x v : E, gE.inner x x v = inner ℝ x v)
  {r R : ℝ} (hr : 0 < r) (hrR : r < R)
  (hs : closedBall (0 : E) R ⊆ e.source)
  (hcoeff : ∀ x ∈ closedBall (0 : E) R,
    gE.euclideanCoefficients x = g.pullbackCoefficients e x)
  (hSphere : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source)

attribute [local instance] Classical.propDecidable
local notation "D" => g.leviCivitaData
local notation "B" => e '' closedBall (0 : E) r
local notation "μ" => (chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure

include he hei hGauss hr hrR hs hcoeff hSphere in
/-- The actual exterior second Green formula, with its negative radial
orientation and coefficient eight. The test may have nonzero boundary value. -/
theorem integral_native_chart_exterior_second_green
    {f φ : M → ℝ} (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    (hφ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ φ) :
    (∫ x in Bᶜ, f x * (-8 * g.leviCivitaData.laplacian φ x) ∂g.volumeMeasure) -
      (∫ x in Bᶜ, (-8 * g.leviCivitaData.laplacian f x) * φ x ∂g.volumeMeasure) =
    8 * ((∫ θ : S, f (e (r • (θ : E))) *
        fderiv ℝ (φ ∘ e) (r • (θ : E)) (θ : E) ∂μ) -
      (∫ θ : S, φ (e (r • (θ : E))) *
        fderiv ℝ (f ∘ e) (r • (θ : E)) (θ : E) ∂μ)) := by
  have h1 := integral_native_chart_exterior_green g gE e he hei hGauss hr hrR hs
    hcoeff hSphere hφ hf (HasCompactSupport.of_compactSpace f)
  have h2 := integral_native_chart_exterior_green g gE e he hei hGauss hr hrR hs
    hcoeff hSphere hf hφ (HasCompactSupport.of_compactSpace φ)
  rw [integral_add (g.leviCivitaData.integrable_mul_laplacian hf hφ
      (HasCompactSupport.of_compactSpace f)).integrableOn
    (g.leviCivitaData.integrable_inner_gradient hf hφ
      (HasCompactSupport.of_compactSpace f)).integrableOn] at h1
  rw [integral_add (g.leviCivitaData.integrable_mul_laplacian hφ hf
      (HasCompactSupport.of_compactSpace φ)).integrableOn
    (g.leviCivitaData.integrable_inner_gradient hφ hf
      (HasCompactSupport.of_compactSpace φ)).integrableOn] at h2
  rw [native_gradient_integral_symm g Bᶜ f φ] at h1
  have hl : (∫ x in Bᶜ, f x * (-8 * g.leviCivitaData.laplacian φ x) ∂g.volumeMeasure) =
      -8 * ∫ x in Bᶜ, f x * g.leviCivitaData.laplacian φ x ∂g.volumeMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  have hr' : (∫ x in Bᶜ, (-8 * g.leviCivitaData.laplacian f x) * φ x ∂g.volumeMeasure) =
      -8 * ∫ x in Bᶜ, φ x * g.leviCivitaData.laplacian f x ∂g.volumeMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  rw [hl, hr']
  linarith only [h1, h2]

include he hei hGauss hr hrR hs hcoeff hSphere in
/-- Equality of actual values and radial derivatives cancels the exterior
Green commutator for the difference of the two original fields. -/
theorem integral_native_chart_exterior_cauchy_difference
    {f h φ : M → ℝ}
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ h)
    (hφ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ φ)
    (hvalue : ∀ θ : S, f (e (r • (θ : E))) = h (e (r • (θ : E))))
    (hnormal : ∀ θ : S,
      fderiv ℝ (f ∘ e) (r • (θ : E)) (θ : E) =
        fderiv ℝ (h ∘ e) (r • (θ : E)) (θ : E)) :
    (∫ x in Bᶜ, f x * (-8 * g.leviCivitaData.laplacian φ x) ∂g.volumeMeasure) -
      (∫ x in Bᶜ, (-8 * g.leviCivitaData.laplacian f x) * φ x ∂g.volumeMeasure) =
    (∫ x in Bᶜ, h x * (-8 * g.leviCivitaData.laplacian φ x) ∂g.volumeMeasure) -
      (∫ x in Bᶜ, (-8 * g.leviCivitaData.laplacian h x) * φ x ∂g.volumeMeasure) := by
  rw [integral_native_chart_exterior_second_green g gE e he hei hGauss hr hrR hs
      hcoeff hSphere hf hφ,
    integral_native_chart_exterior_second_green g gE e he hei hGauss hr hrR hs
      hcoeff hSphere hh hφ]
  simp_rw [hvalue, hnormal]

/-- The closed-manifold Laplacian has the exact coefficient-eight
distributional identity on smooth fields. -/
private theorem integral_native_closed_laplacian_comm
    {f φ : M → ℝ} (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    (hφ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ φ) :
    (∫ x, f x * (-8 * g.leviCivitaData.laplacian φ x) ∂g.volumeMeasure) =
      ∫ x, (-8 * g.leviCivitaData.laplacian f x) * φ x ∂g.volumeMeasure := by
  have h := g.leviCivitaData.integral_mul_laplacian_comm hf hφ
    (HasCompactSupport.of_compactSpace f) (HasCompactSupport.of_compactSpace φ)
  calc
    _ = -8 * ∫ x, f x * g.leviCivitaData.laplacian φ x ∂g.volumeMeasure := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring
    _ = -8 * ∫ x, φ x * g.leviCivitaData.laplacian f x ∂g.volumeMeasure := by rw [h]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring

include he hei hGauss hr hrR hs hcoeff hSphere in
/-- The literal glued function satisfies the distributional equation with
the literal piecewise source. The two actual Cauchy identities eliminate
the interface term; no distributional conclusion is an input. -/
theorem native_chart_cauchy_gluing_no_interface_source
    (c : M → ℝ) (hc : Continuous c) {f h : M → ℝ}
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ h)
    (hvalue : ∀ θ : S, f (e (r • (θ : E))) = h (e (r • (θ : E))))
    (hnormal : ∀ θ : S,
      fderiv ℝ (f ∘ e) (r • (θ : E)) (θ : E) =
        fderiv ℝ (h ∘ e) (r • (θ : E)) (θ : E))
    (φ : M → ℝ) (hφ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ φ) :
    (∫ x, (e '' closedBall (0 : E) r).piecewise f h x * (-8 * g.leviCivitaData.laplacian φ x + c x * φ x)
        ∂g.volumeMeasure) =
      ∫ x, (e '' closedBall (0 : E) r).piecewise (fun y => -8 * g.leviCivitaData.laplacian f y + c y * f y)
        (fun y => -8 * g.leviCivitaData.laplacian h y + c y * h y) x * φ x ∂g.volumeMeasure := by
  classical
  have hB : MeasurableSet B :=
    by simpa only [compl_compl] using (measurableSet_chart_ball_exterior e hrR.le hs).compl
  have hint (v : M → ℝ) (hv : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ v) :
      Integrable (fun x => v x * (-8 * g.leviCivitaData.laplacian φ x)) g.volumeMeasure :=
    (hv.continuous.mul ((g.leviCivitaData.continuous_laplacian hφ).const_mul (-8))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsrc (v : M → ℝ) (hv : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ v) :
      Integrable (fun x => (-8 * g.leviCivitaData.laplacian v x) * φ x) g.volumeMeasure :=
    (((g.leviCivitaData.continuous_laplacian hv).const_mul (-8)).mul hφ.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpot (v : M → ℝ) (hv : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ v) :
      Integrable (fun x => c x * v x * φ x) g.volumeMeasure :=
    ((hc.mul hv.continuous).mul hφ.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsplitL (v : M → ℝ) (hv : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ v) (A : Set M) :
      (∫ x in A, v x * (-8 * g.leviCivitaData.laplacian φ x + c x * φ x) ∂g.volumeMeasure) =
        (∫ x in A, v x * (-8 * g.leviCivitaData.laplacian φ x) ∂g.volumeMeasure) +
          ∫ x in A, c x * v x * φ x ∂g.volumeMeasure := by
    rw [← integral_add (hint v hv).integrableOn (hpot v hv).integrableOn]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  have hsplitR (v : M → ℝ) (hv : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ v) (A : Set M) :
      (∫ x in A, (-8 * g.leviCivitaData.laplacian v x + c x * v x) * φ x ∂g.volumeMeasure) =
        (∫ x in A, (-8 * g.leviCivitaData.laplacian v x) * φ x ∂g.volumeMeasure) +
          ∫ x in A, c x * v x * φ x ∂g.volumeMeasure := by
    rw [← integral_add (hsrc v hv).integrableOn (hpot v hv).integrableOn]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  have hleft : (fun x => (e '' closedBall (0 : E) r).piecewise f h x * (-8 * g.leviCivitaData.laplacian φ x + c x * φ x)) =
      (e '' closedBall (0 : E) r).piecewise (fun x => f x * (-8 * g.leviCivitaData.laplacian φ x + c x * φ x))
        (fun x => h x * (-8 * g.leviCivitaData.laplacian φ x + c x * φ x)) := by
    funext x
    by_cases hx : x ∈ B <;> simp [hx]
  have hright : (fun x => (e '' closedBall (0 : E) r).piecewise
      (fun y => -8 * g.leviCivitaData.laplacian f y + c y * f y)
      (fun y => -8 * g.leviCivitaData.laplacian h y + c y * h y) x * φ x) =
      (e '' closedBall (0 : E) r).piecewise (fun x => (-8 * g.leviCivitaData.laplacian f x + c x * f x) * φ x)
        (fun x => (-8 * g.leviCivitaData.laplacian h x + c x * h x) * φ x) := by
    funext x
    by_cases hx : x ∈ B <;> simp [hx]
  have hiL (v : M → ℝ) (hv : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ v) :
      Integrable (fun x => v x * (-8 * g.leviCivitaData.laplacian φ x + c x * φ x)) g.volumeMeasure := by
    have heq : (fun x => v x * (-8 * g.leviCivitaData.laplacian φ x + c x * φ x)) =
        (fun x => v x * (-8 * g.leviCivitaData.laplacian φ x) + c x * v x * φ x) := by
      funext x; ring
    rw [heq]
    exact (hint v hv).add (hpot v hv)
  have hiR (v : M → ℝ) (hv : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ v) :
      Integrable (fun x => (-8 * g.leviCivitaData.laplacian v x + c x * v x) * φ x) g.volumeMeasure := by
    have heq : (fun x => (-8 * g.leviCivitaData.laplacian v x + c x * v x) * φ x) =
        (fun x => (-8 * g.leviCivitaData.laplacian v x) * φ x + c x * v x * φ x) := by
      funext x; ring
    rw [heq]
    exact (hsrc v hv).add (hpot v hv)
  rw [hleft, hright,
    integral_piecewise hB (hiL f hf).integrableOn (hiL h hh).integrableOn,
    integral_piecewise hB (hiR f hf).integrableOn (hiR h hh).integrableOn,
    hsplitL f hf B, hsplitL h hh Bᶜ, hsplitR f hf B, hsplitR h hh Bᶜ]
  have hglobal := integral_native_closed_laplacian_comm g hf hφ
  have hdecompL := integral_add_compl hB (hint f hf)
  have hdecompR := integral_add_compl hB (hsrc f hf)
  have hexterior := integral_native_chart_exterior_cauchy_difference g gE e he hei hGauss
    hr hrR hs hcoeff hSphere hf hh hφ hvalue hnormal
  linarith only [hglobal, hdecompL, hdecompR, hexterior]

end Boundary

#print axioms integral_native_chart_exterior_second_green
#print axioms integral_native_chart_exterior_cauchy_difference
#print axioms native_chart_cauchy_gluing_no_interface_source

end Yamabe3.Analysis.EuclideanSphereTrace

end -- Close this original proof unit's noncomputable section.


