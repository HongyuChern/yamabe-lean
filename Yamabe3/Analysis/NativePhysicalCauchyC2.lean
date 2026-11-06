import Yamabe3.Analysis.NativeCoordinateNormalC2
import Yamabe3.Analysis.NativeScaledPhysicalCauchy

/-! Genuine normal data of the same C2 field, with induced area,
coefficient eight and physical scaling. No volume-a.e. representative
is restricted to the sphere. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff Bundle ENNReal
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
namespace Yamabe3.Analysis
open Delaunay EuclideanSphereTrace NativeChartSphereMetric
variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
theorem nativeExteriorNormalFluxFunction_eq_neg_radial_of_contMDiffAt_C2
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    {r : ℝ} (hr : 0 < r) (θ : S)
    (hSphere : r • (θ : E) ∈ e.source)
    {W : M → ℝ} (hW : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) 2 W (e (r • (θ : E)))) :
    nativeExteriorNormalFluxFunction e r W θ =
      -8 * fderiv ℝ (W ∘ e) (r • (θ : E)) (θ : E) := by
  unfold nativeExteriorNormalFluxFunction
  rw [map_neg, native_sphere_normal_derivative_C1 e he hr θ hSphere (hW.of_le (by norm_num))]
  ring

/-- Local smoothness on the actual sphere suffices; no global extension of
the representative is used to obtain either continuity assertion. -/
theorem continuous_native_local_sphere_cauchy_C2
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    {r : ℝ} (hr : 0 < r)
    (hSphere : ∀ θ : S, r • (θ : E) ∈ e.source)
    {W : M → ℝ}
    (hW : ∀ θ : S, ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) 2 W (e (r • (θ : E)))) :
    Continuous (fun θ : S => W (e (r • (θ : E)))) ∧
      Continuous (nativeExteriorNormalFluxFunction e r W) := by
  have hWe (θ : S) : ContDiffAt ℝ 2 (W ∘ e) (r • (θ : E)) :=
    ((hW θ).comp (r • (θ : E))
      ((he.contMDiffAt (e.open_source.mem_nhds (hSphere θ))).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).contDiffAt
  have hd : Continuous (fun θ : S => r • (θ : E)) :=
    continuous_subtype_val.const_smul r
  constructor
  · exact continuous_iff_continuousAt.mpr fun θ =>
      (hWe θ).continuousAt.comp (f := fun η : S => r • (η : E)) hd.continuousAt
  · have hD : Continuous (fun θ : S => fderiv ℝ (W ∘ e) (r • (θ : E))) :=
      continuous_iff_continuousAt.mpr fun θ =>
        ((hWe θ).continuousAt_fderiv (by norm_num)).comp
          (f := fun η : S => r • (η : E)) hd.continuousAt
    have hN := (hD.clm_apply continuous_subtype_val).const_mul (-8 : ℝ)
    have heq : nativeExteriorNormalFluxFunction e r W =
        (fun θ : S => -8 * fderiv ℝ (W ∘ e) (r • (θ : E)) (θ : E)) :=
      funext fun θ => nativeExteriorNormalFluxFunction_eq_neg_radial_of_contMDiffAt_C2
        e he hr θ (hSphere θ) (hW θ)
    rw [heq]
    exact hN

/-- The exterior sign and the factor eight are retained in the exact
identity for the actual derivative of the scaled representative. -/
theorem scaled_native_exterior_normal_flux_eq_C2
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    {r : ℝ} (hr : 0 < r) (θ : S)
    (hSphere : r • (θ : E) ∈ e.source)
    {W : M → ℝ} (hW : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) 2 W (e (r • (θ : E)))) :
    r * nativeExteriorNormalFluxFunction e r W θ =
      -8 * fderiv ℝ (fun y : E => W (e (r • y))) (θ : E) (θ : E) := by
  have hWe : ContDiffAt ℝ 2 (W ∘ e) (r • (θ : E)) :=
    (hW.comp (r • (θ : E))
      ((he.contMDiffAt (e.open_source.mem_nhds hSphere)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).contDiffAt
  have hs : HasFDerivAt (fun y : E => r • y)
      (r • ContinuousLinearMap.id ℝ E) (θ : E) :=
    (hasFDerivAt_id (θ : E)).const_smul r
  have hc := (hWe.differentiableAt (by norm_num)).hasFDerivAt.comp (θ : E) hs
  have hD : fderiv ℝ (fun y : E => W (e (r • y))) (θ : E) (θ : E) =
      r * fderiv ℝ (W ∘ e) (r • (θ : E)) (θ : E) := by
    change fderiv ℝ ((W ∘ e) ∘ fun y : E => r • y) (θ : E) (θ : E) = _
    rw [hc.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  rw [hD, nativeExteriorNormalFluxFunction_eq_neg_radial_of_contMDiffAt_C2
    e he hr θ hSphere hW]
  ring


theorem memLp_native_local_normal_C2
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r:ℝ} (hr:0<r) (hSphere:∀θ:S,r • (θ:E)∈e.source)
    {W:M→ℝ} (hW:∀θ:S,ContMDiffAt (𝓡 3) 𝓘(ℝ,ℝ) 2 W (e (r • (θ:E)))) :
    MemLp (nativeExteriorNormalFluxFunction e r W) 2
      (chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure := by
  have hc:=(continuous_native_local_sphere_cauchy_C2 e he hr hSphere hW).2
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  simpa only [IntegrableOn,Measure.restrict_univ,Pi.pow_apply] using!
    (hc.pow 2).continuousOn.integrableOn_compact
      (μ:=(chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure) isCompact_univ

#print axioms nativeExteriorNormalFluxFunction_eq_neg_radial_of_contMDiffAt_C2
#print axioms continuous_native_local_sphere_cauchy_C2
#print axioms scaled_native_exterior_normal_flux_eq_C2
#print axioms memLp_native_local_normal_C2
end Yamabe3.Analysis
