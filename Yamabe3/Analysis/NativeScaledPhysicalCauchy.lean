import Yamabe3.Analysis.NativePhysicalNormalTrace
import Yamabe3.Analysis.NativeH1PhysicalSphereTrace

/-!
# Scaled local jets control the actual physical Cauchy data

The function is required to be smooth only near each point of the retained
chart sphere.  Its value and its coefficient-eight exterior normal flux
are those of that very function, on the sphere metric induced from the
original manifold.  Scaling of the native normal derivative is proved by
the chain rule.  The surface factor r squared then cancels the derivative
factor r inverse in the paired boundary estimate.

The density bound is derived from the supplied coordinate metric.  A finite
family normalized at the pole admits the common bound two at all sufficiently
small radii, with the same metrics and charts throughout.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff Bundle ENNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace Yamabe3.Analysis

open Delaunay EuclideanSphereTrace NativeChartSphereMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem nativeExteriorNormalFluxFunction_eq_neg_radial_of_contMDiffAt
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    {r : ℝ} (hr : 0 < r) (θ : S)
    (hSphere : r • (θ : E) ∈ e.source)
    {W : M → ℝ} (hW : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ W (e (r • (θ : E)))) :
    nativeExteriorNormalFluxFunction e r W θ =
      -8 * fderiv ℝ (W ∘ e) (r • (θ : E)) (θ : E) := by
  unfold nativeExteriorNormalFluxFunction
  rw [map_neg, native_sphere_normal_derivative e he hr θ hSphere hW]
  ring

/-- Local smoothness on the actual sphere suffices; no global extension of
the representative is used to obtain either continuity assertion. -/
theorem continuous_native_local_sphere_cauchy
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    {r : ℝ} (hr : 0 < r)
    (hSphere : ∀ θ : S, r • (θ : E) ∈ e.source)
    {W : M → ℝ}
    (hW : ∀ θ : S, ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ W (e (r • (θ : E)))) :
    Continuous (fun θ : S => W (e (r • (θ : E)))) ∧
      Continuous (nativeExteriorNormalFluxFunction e r W) := by
  have hWe (θ : S) : ContDiffAt ℝ ∞ (W ∘ e) (r • (θ : E)) :=
    ((hW θ).comp (r • (θ : E))
      (he.contMDiffAt (e.open_source.mem_nhds (hSphere θ)))).contDiffAt
  have hd : Continuous (fun θ : S => r • (θ : E)) :=
    continuous_subtype_val.const_smul r
  constructor
  · exact continuous_iff_continuousAt.mpr fun θ =>
      (hWe θ).continuousAt.comp (f := fun η : S => r • (η : E)) hd.continuousAt
  · have hD : Continuous (fun θ : S => fderiv ℝ (W ∘ e) (r • (θ : E))) :=
      continuous_iff_continuousAt.mpr fun θ =>
        ((hWe θ).continuousAt_fderiv (by simp)).comp
          (f := fun η : S => r • (η : E)) hd.continuousAt
    have hN := (hD.clm_apply continuous_subtype_val).const_mul (-8 : ℝ)
    have heq : nativeExteriorNormalFluxFunction e r W =
        (fun θ : S => -8 * fderiv ℝ (W ∘ e) (r • (θ : E)) (θ : E)) :=
      funext fun θ => nativeExteriorNormalFluxFunction_eq_neg_radial_of_contMDiffAt
        e he hr θ (hSphere θ) (hW θ)
    rw [heq]
    exact hN

/-- The exterior sign and the factor eight are retained in the exact
identity for the actual derivative of the scaled representative. -/
theorem scaled_native_exterior_normal_flux_eq
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    {r : ℝ} (hr : 0 < r) (θ : S)
    (hSphere : r • (θ : E) ∈ e.source)
    {W : M → ℝ} (hW : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ W (e (r • (θ : E)))) :
    r * nativeExteriorNormalFluxFunction e r W θ =
      -8 * fderiv ℝ (fun y : E => W (e (r • y))) (θ : E) (θ : E) := by
  have hWe : ContDiffAt ℝ ∞ (W ∘ e) (r • (θ : E)) :=
    (hW.comp (r • (θ : E))
      (he.contMDiffAt (e.open_source.mem_nhds hSphere))).contDiffAt
  have hs : HasFDerivAt (fun y : E => r • y)
      (r • ContinuousLinearMap.id ℝ E) (θ : E) :=
    (hasFDerivAt_id (θ : E)).const_smul r
  have hc := (hWe.differentiableAt (by simp)).hasFDerivAt.comp (θ : E) hs
  have hD : fderiv ℝ (fun y : E => W (e (r • y))) (θ : E) (θ : E) =
      r * fderiv ℝ (W ∘ e) (r • (θ : E)) (θ : E) := by
    change fderiv ℝ ((W ∘ e) ∘ fun y : E => r • y) (θ : E) (θ : E) = _
    rw [hc.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  rw [hD, nativeExteriorNormalFluxFunction_eq_neg_radial_of_contMDiffAt
    e he hr θ hSphere hW]
  ring

/-- Only orders zero and one of the true scaled jets are consumed.  Thus
the output of the H4-to-two-jets estimate applies without changing its
solution, chart, radius, or representative. -/
theorem native_scaled_cauchy_pointwise_of_jets
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    {r A : ℝ} (hr : 0 < r)
    (hSphere : ∀ θ : S, r • (θ : E) ∈ e.source)
    {W : M → ℝ}
    (hW : ∀ θ : S, ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ W (e (r • (θ : E))))
    (hjets : ∀ n ≤ 1, ∀ z ∈ sphere (0 : E) 1,
      ‖iteratedFDeriv ℝ n (fun y => W (e (r • y))) z‖ ≤ A) :
    ∀ θ : S, |W (e (r • (θ : E)))| ≤ A ∧
      |r * nativeExteriorNormalFluxFunction e r W θ| ≤ 8 * A := by
  intro θ
  constructor
  · simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
      hjets 0 (by norm_num) θ θ.property
  · rw [scaled_native_exterior_normal_flux_eq e he hr θ (hSphere θ) (hW θ), abs_mul]
    have hDn : ‖fderiv ℝ (fun y : E => W (e (r • y))) (θ : E)‖ ≤ A := by
      simpa only [norm_iteratedFDeriv_one] using hjets 1 (by norm_num) θ θ.property
    have hθn : ‖(θ : E)‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using θ.property
    have happ := (fderiv ℝ (fun y : E => W (e (r • y))) (θ : E)).le_opNorm (θ : E)
    rw [hθn, mul_one, Real.norm_eq_abs] at happ
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
    exact mul_le_mul_of_nonneg_left (happ.trans hDn) (by norm_num)

/-- A scalar continuous function bounded by A on the actual sphere has
the physical area estimate, with the ambient density comparison proved
from the original sphere metric. -/
theorem integral_native_sphere_sq_le_of_pointwise
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r C A : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hSphere : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source)
    (hcoeff : ∀ θ : S, gE.euclideanCoefficients (r • (θ : E)) =
      g.pullbackCoefficients e (r • (θ : E)))
    (hGauss : ∀ (θ : S) (v : E), gE.inner (r • (θ : E)) (r • (θ : E)) v =
      inner ℝ (r • (θ : E)) v)
    (hρ : ∀ θ : S, gE.pullbackVolumeDensity id (r • (θ : E)) ≤ C)
    {f : S → ℝ} (hf : Continuous f) (hbound : ∀ θ, |f θ| ≤ A) :
    (∫ θ : S, f θ ^ 2 ∂(chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure) ≤
      C * SpherePolar.angularVolume.real univ * r ^ 2 * A ^ 2 := by
  have hfi : Integrable (fun θ : S => f θ ^ 2) SpherePolar.angularVolume := by
    simpa only [integrableOn_univ, Pi.pow_apply] using!
      (hf.pow 2).continuousOn.integrableOn_compact
        (μ := SpherePolar.angularVolume) (isCompact_univ : IsCompact (univ : Set S))
  have hμ := SpherePolar.chartRadiusMetric_volume_le_nativeAngular
    g gE e he hei hr.ne' hC hSphere hcoeff hGauss hρ
  have h1 := integral_mono_measure hμ (Eventually.of_forall fun θ => sq_nonneg (f θ))
    (hfi.smul_measure ENNReal.ofReal_ne_top)
  have h2 : (∫ θ : S, f θ ^ 2 ∂SpherePolar.angularVolume) ≤ SpherePolar.angularVolume.real univ * A ^ 2 := by
    have h := integral_mono hfi (integrable_const (A ^ 2)) (fun θ => by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (f θ)) hA).mpr (hbound θ))
    simpa only [sq_abs, integral_const, smul_eq_mul] using! h
  calc
    _ ≤ (C * r ^ 2) * ∫ θ : S, f θ ^ 2 ∂SpherePolar.angularVolume := by
      simpa only [integral_smul_measure,
        ENNReal.toReal_ofReal (mul_nonneg hC (sq_nonneg r)), smul_eq_mul] using! h1
    _ ≤ (C * r ^ 2) * (SpherePolar.angularVolume.real univ * A ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hC (sq_nonneg r))
    _ = _ := by ring

/-- The value and coefficient-eight outward normal data are bounded for
the same locally smooth function in the actual induced area measure.
The radius appears exactly as required by scaling of first derivatives. -/
theorem native_physical_cauchy_sq_le_scaled_jets
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r C A : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hSphere : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source)
    (hcoeff : ∀ θ : S, gE.euclideanCoefficients (r • (θ : E)) =
      g.pullbackCoefficients e (r • (θ : E)))
    (hGauss : ∀ (θ : S) (v : E), gE.inner (r • (θ : E)) (r • (θ : E)) v =
      inner ℝ (r • (θ : E)) v)
    (hρ : ∀ θ : S, gE.pullbackVolumeDensity id (r • (θ : E)) ≤ C)
    {W : M → ℝ}
    (hW : ∀ θ : S, ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ W (e (r • (θ : E))))
    (hjets : ∀ n ≤ 1, ∀ z ∈ sphere (0 : E) 1,
      ‖iteratedFDeriv ℝ n (fun y => W (e (r • y))) z‖ ≤ A) :
    ((∫ θ : S, W (e (r • (θ : E))) ^ 2
        ∂(chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure) / r ^ 2 +
      ∫ θ : S, nativeExteriorNormalFluxFunction e r W θ ^ 2
        ∂(chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure) ≤
      65 * C * SpherePolar.angularVolume.real univ * A ^ 2 := by
  let μ := (chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure
  obtain ⟨hVcont, hNcont⟩ := continuous_native_local_sphere_cauchy e he hr hSphere hW
  have hb := native_scaled_cauchy_pointwise_of_jets e he hr hSphere hW hjets
  have hV := integral_native_sphere_sq_le_of_pointwise g gE e he hei hr hC hA
    hSphere hcoeff hGauss hρ hVcont (fun θ => (hb θ).1)
  have hN := integral_native_sphere_sq_le_of_pointwise g gE e he hei hr hC
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hA)
    hSphere hcoeff hGauss hρ (hNcont.const_mul r) (fun θ => (hb θ).2)
  have hNscale : (∫ θ : S, (r * nativeExteriorNormalFluxFunction e r W θ) ^ 2 ∂μ) =
      r ^ 2 * ∫ θ : S, nativeExteriorNormalFluxFunction e r W θ ^ 2 ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun θ => by ring
  change (∫ θ : S, (r * nativeExteriorNormalFluxFunction e r W θ) ^ 2 ∂μ) ≤ _ at hN
  rw [hNscale] at hN
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hV' : (∫ θ : S, W (e (r • (θ : E))) ^ 2 ∂μ) / r ^ 2 ≤
      C * SpherePolar.angularVolume.real univ * A ^ 2 := by
    apply (div_le_iff₀ hr2).mpr
    calc
      _ ≤ C * SpherePolar.angularVolume.real univ * r ^ 2 * A ^ 2 := hV
      _ = _ := by ring
  have hN' : (∫ θ : S, nativeExteriorNormalFluxFunction e r W θ ^ 2 ∂μ) ≤
      64 * C * SpherePolar.angularVolume.real univ * A ^ 2 := by
    apply (mul_le_mul_iff_right₀ hr2).mp
    calc
      _ ≤ C * SpherePolar.angularVolume.real univ * r ^ 2 * (8 * A) ^ 2 := hN
      _ = _ := by ring
  change _ ≤ _
  linarith only [hV', hN']

/-- The physical value and normal bounds respect the same weight as the
scaled interior jets.  Cancellation uses positive-radius real powers. -/
theorem native_weighted_physical_cauchy_sq_le_scaled_jets
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r C A a : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hSphere : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source)
    (hcoeff : ∀ θ : S, gE.euclideanCoefficients (r • (θ : E)) =
      g.pullbackCoefficients e (r • (θ : E)))
    (hGauss : ∀ (θ : S) (v : E), gE.inner (r • (θ : E)) (r • (θ : E)) v =
      inner ℝ (r • (θ : E)) v)
    (hρ : ∀ θ : S, gE.pullbackVolumeDensity id (r • (θ : E)) ≤ C)
    {W : M → ℝ}
    (hW : ∀ θ : S, ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ W (e (r • (θ : E))))
    (hjets : ∀ n ≤ 1, ∀ z ∈ sphere (0 : E) 1,
      ‖iteratedFDeriv ℝ n (fun y => W (e (r • y))) z‖ ≤ A * r ^ (-a)) :
    r ^ (2 * a) *
      ((∫ θ : S, W (e (r • (θ : E))) ^ 2
          ∂(chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure) / r ^ 2 +
        ∫ θ : S, nativeExteriorNormalFluxFunction e r W θ ^ 2
          ∂(chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure) ≤
      65 * C * SpherePolar.angularVolume.real univ * A ^ 2 := by
  have hb := native_physical_cauchy_sq_le_scaled_jets g gE e he hei hr hC
    (mul_nonneg hA (Real.rpow_nonneg hr.le _)) hSphere hcoeff hGauss hρ hW hjets
  have hw : r ^ (2 * a) * (r ^ (-a)) ^ 2 = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le, ← Real.rpow_add hr]
    convert Real.rpow_zero r using 1 <;> ring
  have hm := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hr.le (2 * a))
  apply hm.trans_eq
  calc
    r ^ (2 * a) * (65 * C * SpherePolar.angularVolume.real univ * (A * r ^ (-a)) ^ 2) =
        (65 * C * SpherePolar.angularVolume.real univ * A ^ 2) *
          (r ^ (2 * a) * (r ^ (-a)) ^ 2) := by ring
    _ = _ := by rw [hw, mul_one]

/-- A single small radius controls the density of every retained metric.
The metrics themselves are not changed.  This can be intersected with any
already proved geometric, source, or neck-scale radius. -/
theorem exists_uniform_finite_normalized_sphere_density_bound
    {ι : Type*} (Λ : Finset ι) (gE : ι → RiemannianMetric 3 E)
    (hρ0 : ∀ p ∈ Λ, (gE p).pullbackVolumeDensity id 0 = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ → ∀ p ∈ Λ, ∀ θ : S,
      (gE p).pullbackVolumeDensity id (r • (θ : E)) ≤ 2 := by
  have hevent : ∀ᶠ x : E in 𝓝 0, ∀ p ∈ Λ,
      (gE p).pullbackVolumeDensity id x < 2 := by
    rw [eventually_all_finset]
    intro p hp
    have hc : ContinuousAt ((gE p).pullbackVolumeDensity id) 0 :=
      ((gE p).contDiffAt_pullbackVolumeDensity contMDiffAt_id
        (by rw [mfderiv_id]; exact Function.injective_id)).1.continuousAt
    exact hc (Iio_mem_nhds (by rw [hρ0 p hp]; norm_num))
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ p hp θ
  apply le_of_lt
  apply hδb _ p hp
  simpa only [mem_ball, dist_zero_right, norm_sphereTrace_radial θ hr.le] using hrδ

#print axioms native_scaled_cauchy_pointwise_of_jets
#print axioms native_physical_cauchy_sq_le_scaled_jets
#print axioms native_weighted_physical_cauchy_sq_le_scaled_jets
#print axioms exists_uniform_finite_normalized_sphere_density_bound

end Yamabe3.Analysis
