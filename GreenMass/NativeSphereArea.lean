import GreenMass.NativePolarMap
import PoincareLib.Geometry.Riemannian.Measure.HausdorffDensity
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Topology.PartialChartMeasurable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Polar area equals the volume of the actual induced sphere metric

The proof computes the Lebesgue volume of a cone by the genuine polar map,
uses its proved native Gram Jacobian, and integrates the radial square.
The local formula agrees with native Riemannian volume in every smooth
sphere chart.  A countable chart cover then gives equality of measures.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory Poincare.EuclideanSpace Poincare.Coarea
open scoped Manifold ContDiff Bundle ENNReal Pointwise

namespace GreenMass.NativeSphereArea

open NativeSphereGeometry NativePolarMap

theorem lintegral_radial_square :
    (∫⁻ r : ℝ in Ioo 0 1, ENNReal.ofReal (r ^ 2)) = (3 : ℝ≥0∞)⁻¹ := by
  have hic : IntegrableOn (fun r : ℝ => r ^ 2) (Icc 0 1) :=
    (continuous_id.pow 2).integrableOn_Icc
  have hi : IntegrableOn (fun r : ℝ => r ^ 2) (Ioo 0 1) :=
    hic.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun r => sq_nonneg r))]
  have hv : (∫ r : ℝ in Ioo 0 1, r ^ 2) = (1 / 3 : ℝ) := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num), integral_pow]
    norm_num
  rw [hv, one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

theorem lintegral_polarDomain_factor {s : Set V} {g : V → ℝ≥0∞}
    (hg : AEMeasurable g (volume.restrict s)) :
    (∫⁻ x : E in polarDomain s, ENNReal.ofReal ((x 0) ^ 2) * g (euclideanTail x)) =
      (3 : ℝ≥0∞)⁻¹ * ∫⁻ z in s, g z := by
  have hp : (euclideanConsEquiv 2) ⁻¹' polarDomain s = (Ioo (0 : ℝ) 1) ×ˢ s := by
    ext p
    simp [polarDomain]
  have hchange := (volumePreserving_euclideanConsEquiv 2).setLIntegral_comp_preimage_emb
    (euclideanConsEquiv 2).measurableEmbedding
    (fun x : E => ENNReal.ofReal ((x 0) ^ 2) * g (euclideanTail x)) (polarDomain s)
  rw [hp] at hchange
  simp only [euclideanConsEquiv_apply, euclideanCons_zero, euclideanTail_cons] at hchange
  rw [← hchange]
  change (∫⁻ p : ℝ × V in (Ioo (0 : ℝ) 1) ×ˢ s,
    ENNReal.ofReal (p.1 ^ 2) * g p.2 ∂(volume.prod volume)) = _
  rw [← Measure.prod_restrict]
  have hf : AEMeasurable (fun r : ℝ => ENNReal.ofReal (r ^ 2))
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ((continuous_id.pow 2).measurable.ennreal_ofReal).aemeasurable
  calc
    _ = (∫⁻ r : ℝ in Ioo 0 1, ENNReal.ofReal (r ^ 2)) * ∫⁻ z in s, g z :=
      lintegral_prod_mul hf hg
    _ = _ := by rw [lintegral_radial_square]

/-- The native polar Jacobian supplies the coordinate density for the actual
cone measure used in the pre-existing ADM modules. -/
theorem sphereArea_image_eq_lintegral_density
    (e : OpenPartialHomeomorph V S)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    {s : Set V} (hs : MeasurableSet s) (hse : s ⊆ e.source) :
    SphereMeasure.sphereArea (e '' s) =
      ∫⁻ z in s, ENNReal.ofReal (sphereMetric.pullbackVolumeDensity e z) := by
  have hD : e.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (sphereMetric.pullbackVolumeDensity e) s := by
    intro z hz
    exact (sphereMetric.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds (hse hz)))
      (hD.mfderiv_injective (hse hz))).1.continuousAt.continuousWithinAt
  have hρm : AEMeasurable (fun z => ENNReal.ofReal (sphereMetric.pullbackVolumeDensity e z))
      (volume.restrict s) :=
    (ENNReal.continuous_ofReal.comp_continuousOn hρ).aemeasurable hs
  have hpd (x : E) (hx : x ∈ polarDomain s) :
      MDifferentiableAt (𝓡 2) (𝓡 2) e (euclideanTail x) :=
    (he.contMDiffAt (e.open_source.mem_nhds (hse hx.2))).mdifferentiableAt (by simp)
  rw [SphereMeasure.sphereArea_apply (e.measurableSet_image_of_subset_source hs hse),
    ← polarMap_image,
    ← lintegral_abs_det_fderiv_eq_addHaar_image (volume : Measure E)
      (measurableSet_polarDomain hs)
      (fun x hx => (hasFDerivAt_polarMap (hpd x hx)).hasFDerivWithinAt)
      (polarMap_injOn e hse)]
  calc
    3 * (∫⁻ x in polarDomain s, ENNReal.ofReal |(polarDerivative e x).det|) =
        3 * (∫⁻ x in polarDomain s, ENNReal.ofReal ((x 0) ^ 2) *
          ENNReal.ofReal (sphereMetric.pullbackVolumeDensity e (euclideanTail x))) := by
      congr 1
      apply setLIntegral_congr_fun (measurableSet_polarDomain hs)
      intro x hx
      exact (congrArg ENNReal.ofReal (polarDerivative_abs_det
        (e := e) (x := x) (hpd x hx))).trans (ENNReal.ofReal_mul (sq_nonneg (x 0)))
    _ = ∫⁻ z in s, ENNReal.ofReal (sphereMetric.pullbackVolumeDensity e z) := by
      rw [lintegral_polarDomain_factor hρm, ← mul_assoc,
        ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]

theorem sphereArea_restrict_chart
    (e : OpenPartialHomeomorph V S)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target) :
    SphereMeasure.sphereArea.restrict e.target = sphereMetric.volumeMeasure.restrict e.target := by
  ext t ht
  rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
  let s : Set V := e ⁻¹' t ∩ e.source
  have hs : MeasurableSet s := e.measurableSet_preimage_inter_source ht
  have hse : s ⊆ e.source := inter_subset_right
  have himage : e '' s = t ∩ e.target := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz.1, e.map_source hz.2⟩
    · intro hy
      exact ⟨e.symm y, ⟨by simpa only [mem_preimage, e.right_inv hy.2] using hy.1,
        e.map_target hy.2⟩, e.right_inv hy.2⟩
  rw [← himage, sphereArea_image_eq_lintegral_density e he hei hs hse,
    sphereMetric.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity e he hei hs hse]

/-- Equality with the actual native induced Riemannian area measure.
The native volume is the normalized intrinsic Hausdorff measure of the
induced metric; its coordinate density is proved upstream, not assumed. -/
theorem sphereArea_eq_native_area : SphereMeasure.sphereArea = sphereMetric.volumeMeasure := by
  have hcover : (univ : Set S) ⊆ ⋃ p : S, (chartAt V p).source := by
    intro p _
    exact mem_iUnion.mpr ⟨p, mem_chart_source V p⟩
  obtain ⟨t, htc, htcover⟩ := isCompact_univ.isLindelof.elim_countable_subcover
    (fun p : S => (chartAt V p).source) (fun p => (chartAt V p).open_source) hcover
  apply Measure.ext_of_biUnion_eq_univ htc (eq_univ_of_univ_subset htcover)
  intro p _
  exact sphereArea_restrict_chart (chartAt V p).symm contMDiffOn_chart_symm contMDiffOn_chart

/-- The induced native area has the exact standard `4π` normalization. -/
theorem native_area_univ :
    sphereMetric.volumeMeasure univ = ENNReal.ofReal (4 * Real.pi) := by
  rw [← sphereArea_eq_native_area]
  exact SphereMeasure.sphereArea_univ

#print axioms lintegral_radial_square
#print axioms lintegral_polarDomain_factor
#print axioms sphereArea_image_eq_lintegral_density
#print axioms sphereArea_eq_native_area
#print axioms native_area_univ

end GreenMass.NativeSphereArea
