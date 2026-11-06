import Yamabe3.Analysis.NativeCoordinateNormalTrace
import Yamabe3.Analysis.NativeChartSphereMetric
import Yamabe3.Analysis.NativeGaussSphereTrace

/-!
# The actual exterior normal flux as an L2 function on the native sphere

The vector is the negative of the existing chart radial normal. The latter
has already been proved to be the genuine unit normal under the actual
Gauss coefficient identity. Its sign differentiates the chart radius to -1.
The scalar derivative is identified by the native chain rule, and its L2
class uses the original manifold's induced sphere area. Its derivative
bound is transferred through the proved same-metric area identity.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff Bundle ENNReal RealInnerProductSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace Yamabe3.Analysis

open PoincareMT.LeviCivitaData.Dirichlet Delaunay EuclideanSphereTrace NativeChartSphereMetric
open GreenMass.NativeGaussSphereArea

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- The sign of the existing unit chart normal appropriate to the exterior
of a chart ball. Orthogonality and orientation concern the actual native
metric and actual native radius derivative. -/
theorem nativeExteriorNormal_geometry
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {x : E} (hxs : x ∈ e.source) (hx : x ≠ 0)
    (hGauss : ∀ v : E, g.pullbackCoefficients e x x v = inner ℝ x v) :
    g.inner (e x) (-chartRadialNormal e x) (-chartRadialNormal e x) = 1 ∧
    (∀ v : E, inner ℝ x v = 0 →
      g.inner (e x) (-chartRadialNormal e x) (mfderiv (𝓡 3) (𝓡 3) e x v) = 0) ∧
    mvfderiv (𝓡 3) (coordinateExtension e (fun y : E => ‖y‖)) (e x)
      (-chartRadialNormal e x) = -1 := by
  constructor
  · simpa only [map_neg, neg_apply, neg_neg] using chartRadialNormal_unit g e hx hGauss
  constructor
  · intro v hv
    simp only [map_neg, neg_apply, chartRadialNormal_orthogonal g e x v hGauss hv, neg_zero]
  · rw [map_neg, chartRadialNormal_outward e he hei hxs hx]

/-- The coefficient-eight outward flux, with the existing actual native
normal vector, before passing to its L2 class. -/
def nativeExteriorNormalFluxFunction (e : OpenPartialHomeomorph E M) (r : ℝ)
    (W : M → ℝ) : S → ℝ := fun θ =>
  8 * mvfderiv (𝓡 3) W (e (r • (θ : E))) (-chartRadialNormal e (r • (θ : E)))

theorem nativeExteriorNormalFluxFunction_eq_neg_radial
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    {r : ℝ} (hr : 0 < r)
    (hSphere : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source)
    {W : M → ℝ} (hW : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ W) (θ : S) :
    nativeExteriorNormalFluxFunction e r W θ =
      -8 * fderiv ℝ (W ∘ e) (r • (θ : E)) (θ : E) := by
  unfold nativeExteriorNormalFluxFunction
  rw [map_neg, native_sphere_normal_derivative e he hr θ (hSphere θ) hW.contMDiffAt]
  ring

theorem continuous_nativeExteriorNormalFluxFunction
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    {r : ℝ} (hr : 0 < r)
    (hSphere : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source)
    {W : M → ℝ} (hW : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ W) :
    Continuous (nativeExteriorNormalFluxFunction e r W) := by
  have hWe : ContDiffOn ℝ ∞ (W ∘ e) e.source := (hW.comp_contMDiffOn he).contDiffOn
  have hD := continuous_restriction_to_sphere e.open_source
    (hWe.fderiv_of_isOpen (m := ∞) e.open_source (by simp)).continuousOn r hSphere
  have hN : Continuous (fun θ : S => fderiv ℝ (W ∘ e) (r • (θ : E)) (θ : E)) :=
    hD.clm_apply continuous_subtype_val
  have heq : nativeExteriorNormalFluxFunction e r W =
      (fun θ : S => -8 * fderiv ℝ (W ∘ e) (r • (θ : E)) (θ : E)) :=
    funext (nativeExteriorNormalFluxFunction_eq_neg_radial e he hr hSphere hW)
  rw [heq]
  exact hN.const_mul (-8)

theorem memLp_nativeExteriorNormalFluxFunction
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r : ℝ} (hr : 0 < r)
    (hSphere : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source)
    {W : M → ℝ} (hW : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ W) :
    MemLp (nativeExteriorNormalFluxFunction e r W) 2
      (chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure := by
  have hc := continuous_nativeExteriorNormalFluxFunction e he hr hSphere hW
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  simpa only [IntegrableOn, Measure.restrict_univ, Pi.pow_apply] using!
    (hc.pow 2).continuousOn.integrableOn_compact
      (μ := (chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure) isCompact_univ

def nativeExteriorNormalFluxL2
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r : ℝ} (hr : 0 < r)
    (hSphere : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source)
    (W : M → ℝ) (hW : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ W) :
    Lp ℝ 2 (chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure :=
  (memLp_nativeExteriorNormalFluxFunction g e he hei hr hSphere hW).toLp
    (nativeExteriorNormalFluxFunction e r W)

theorem nativeExteriorNormalFluxL2_coe_ae
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r : ℝ} (hr : 0 < r)
    (hSphere : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source)
    (W : M → ℝ) (hW : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ W) :
    (nativeExteriorNormalFluxL2 g e he hei hr hSphere W hW : S → ℝ)
      =ᵐ[(chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure]
        nativeExteriorNormalFluxFunction e r W :=
  (memLp_nativeExteriorNormalFluxFunction g e he hei hr hSphere hW).coeFn_toLp

theorem nativeExteriorNormalFluxL2_norm_sq
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r : ℝ} (hr : 0 < r)
    (hSphere : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source)
    (W : M → ℝ) (hW : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ W) :
    ‖nativeExteriorNormalFluxL2 g e he hei hr hSphere W hW‖ ^ 2 =
      64 * (∫ θ : S, (fderiv ℝ (W ∘ e) (r • (θ : E)) (θ : E)) ^ 2
        ∂(chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [nativeExteriorNormalFluxL2_coe_ae g e he hei hr hSphere W hW] with θ hθ
  rw [hθ, nativeExteriorNormalFluxFunction_eq_neg_radial e he hr hSphere hW]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- A genuine same-function, same-native-area normal estimate. The factor
1536 is 8 squared times the proved radial derivative trace constant 24. -/
theorem nativeExteriorNormalFluxL2_norm_sq_le_scaled_energy
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hKs : sphereTraceAnnulus (r / 2) (3 * r / 2) ⊆ e.source)
    (hSphere : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source)
    (hcoeff : ∀ θ : S, gE.euclideanCoefficients (r • (θ : E)) =
      g.pullbackCoefficients e (r • (θ : E)))
    (hGauss : ∀ (θ : S) (v : E), gE.inner (r • (θ : E)) (r • (θ : E)) v =
      inner ℝ (r • (θ : E)) v)
    (hρ : ∀ θ : S, gE.pullbackVolumeDensity id (r • (θ : E)) ≤ C)
    (W : M → ℝ) (hW : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ W) :
    ‖nativeExteriorNormalFluxL2 g e he hei hr hSphere W hW‖ ^ 2 ≤
      (1536 * C / r) * ∫ x in sphereTraceAnnulus (r / 2) (3 * r / 2),
        ‖fderiv ℝ (W ∘ e) x‖ ^ 2 + r ^ 2 * ‖fderiv ℝ (fderiv ℝ (W ∘ e)) x‖ ^ 2 := by
  rw [nativeExteriorNormalFluxL2_norm_sq,
    chartRadiusMetric_eq_gaussRadiusMetric g gE e he hei r hr.ne' hSphere hcoeff]
  have hb := (integral_gaussRadiusMetric_cauchy_sq_le_scaled_energy gE hr hC hGauss hρ
    e.open_source hKs (hW.comp_contMDiffOn he).contDiffOn).2
  have h := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 64)
  convert h using 1 <;> (first | rfl | ring)

#print axioms nativeExteriorNormal_geometry
#print axioms nativeExteriorNormalFluxFunction_eq_neg_radial
#print axioms memLp_nativeExteriorNormalFluxFunction
#print axioms nativeExteriorNormalFluxL2_norm_sq_le_scaled_energy

end Yamabe3.Analysis
