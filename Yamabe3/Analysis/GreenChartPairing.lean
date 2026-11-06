import Yamabe3.Analysis.Green.NativeChartIntegralTransfer
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateRepresentative

/-!
# Native chart pairing with measurable, possibly singular multipliers

The source function only needs actual measurability; it need not be smooth
at the singular point. The source and target measures are the retained
metric volumes, with the actual pullback density in the intermediate formula.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace Yamabe3.Parametrix

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet
open Yamabe3.Analysis.GreenParametrix

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- Change of variables for a genuine zero-extended coordinate function.
Measurability of both factors suffices; neither must be smooth at the other
factor’s singular point. -/
theorem integral_mul_coordinateExtension_eq_density_measurable (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {f : E → ℝ} (hf : Measurable f) {φ : M → ℝ} (hφ : Measurable φ) :
    (∫ y, φ y * coordinateExtension e f y ∂g.volumeMeasure) =
      ∫ x in e.source, (φ (e x) * f x) * g.pullbackVolumeDensity e x := by
  have hmap := g.map_restrict_volumeMeasure_symm e he hei
  have hm : AEStronglyMeasurable (fun x => φ (e x) * f x)
      ((g.volumeMeasure.restrict e.target).map e.symm) := by
    rw [hmap]
    exact ((hφ.comp_aemeasurable (e.continuousOn.aemeasurable
      e.open_source.measurableSet)).aestronglyMeasurable).mul hf.aestronglyMeasurable
  have hi := integral_map
    (e.symm.continuousOn.aemeasurable e.open_target.measurableSet) hm
  change (∫ x, φ (e x) * f x ∂(g.volumeMeasure.restrict e.target).map e.symm) =
    ∫ y in e.target, φ (e (e.symm y)) * f (e.symm y) ∂g.volumeMeasure at hi
  rw [hmap] at hi
  have hD : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) e.source := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hx))
      (hD.mfderiv_injective hx)).1.continuousAt.continuousWithinAt
  calc
    _ = ∫ y in e.target, φ y * coordinateExtension e f y ∂g.volumeMeasure := by
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro y hy
      simp only [coordinateExtension, indicator_of_notMem hy, mul_zero]
    _ = ∫ y in e.target, φ (e (e.symm y)) * f (e.symm y) ∂g.volumeMeasure := by
      apply setIntegral_congr_fun e.open_target.measurableSet
      intro y hy
      dsimp only
      rw [e.right_inv hy, coordinateExtension_apply e f hy]
    _ = ∫ x in e.source, φ (e x) * f x ∂volume.withDensity
        (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x)) := hi.symm
    _ = _ := by
      rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
        (μ := volume) (f := fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))
        (s := e.source)
        ((ENNReal.continuous_ofReal.comp_continuousOn hρ).aemeasurable
          e.open_source.measurableSet)
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
        (fun x => φ (e x) * f x) e.open_source.measurableSet]
      apply setIntegral_congr_fun e.open_source.measurableSet
      intro x _
      simp [RiemannianMetric.pullbackVolumeDensity, ENNReal.toReal_ofReal,
        Real.sqrt_nonneg, smul_eq_mul, mul_comm]

/-- Where the actual coordinate metric agrees in volume density on the
support, both sides of the change of variables use native metric volumes. -/
theorem integral_mul_coordinateExtension_eq_native_measurable (g : RiemannianMetric 3 M)
    (gE : RiemannianMetric 3 E) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {f : E → ℝ} (hf : Measurable f) (hfs : tsupport f ⊆ e.source)
    (hρ : ∀ x ∈ tsupport f,
      gE.pullbackVolumeDensity id x = g.pullbackVolumeDensity e x)
    {φ : M → ℝ} (hφ : Measurable φ) :
    (∫ y, φ y * coordinateExtension e f y ∂g.volumeMeasure) =
      ∫ x, φ (e x) * f x ∂gE.volumeMeasure := by
  rw [integral_mul_coordinateExtension_eq_density_measurable g e he hei hf hφ,
    native_integral_eq_density gE]
  calc
    _ = ∫ x in e.source, (φ (e x) * f x) * gE.pullbackVolumeDensity id x := by
      apply setIntegral_congr_fun e.open_source.measurableSet
      intro x _
      dsimp only
      by_cases hx : x ∈ tsupport f
      · rw [hρ x hx]
      · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, zero_mul]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hfs h))
      simp only [hf0, mul_zero, zero_mul]

/-- Actual measurable native L2 functions pull back to their actual chart
functions, rather than only to a chosen Lp class representative. -/
theorem memLp_pullback_density_of_measurable (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {φ : M → ℝ} (hφ : Measurable φ) (hf : MemLp φ 2 g.volumeMeasure) :
    MemLp (fun x => φ (e x)) 2
      ((volume.withDensity (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))).restrict
        e.source) := by
  rw [← g.map_restrict_volumeMeasure_symm e he hei]
  have hm : AEStronglyMeasurable (fun x => φ (e x))
      ((g.volumeMeasure.restrict e.target).map e.symm) := by
    rw [g.map_restrict_volumeMeasure_symm e he hei]
    exact (hφ.comp_aemeasurable
      (e.continuousOn.aemeasurable e.open_source.measurableSet)).aestronglyMeasurable
  apply (memLp_map_measure_iff hm
    (e.symm.continuousOn.aemeasurable e.open_target.measurableSet)).mpr
  apply MemLp.ae_eq (hf_Lp := hf.restrict e.target)
  filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
  simp only [Function.comp_apply, e.right_inv hy]

omit [T3Space M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] in
/-- Restricting to an actual measurable chart subset before zero extension
avoids any claim about the chart's arbitrary values outside its source. -/
theorem measurable_chart_indicator
    (e : OpenPartialHomeomorph E M) {K : Set E}
    (hK : MeasurableSet K) (hKs : K ⊆ e.source)
    {φ : M → ℝ} (hφ : Measurable φ) : Measurable (K.indicator (φ ∘ e)) := by
  apply measurable_of_restrict_of_restrict_compl hK
  · have hc : Measurable (fun x : K => φ (e x)) :=
      hφ.comp ((e.continuousOn.mono hKs).domRestrict.measurable)
    change Measurable (fun x : K => K.indicator (φ ∘ e) x)
    convert hc using 1
    funext x
    exact indicator_of_mem x.property _
  · change Measurable (fun x : ↥(Kᶜ) => K.indicator (φ ∘ e) x)
    convert (measurable_const : Measurable (fun _ : ↥(Kᶜ) => (0 : ℝ))) using 1
    funext x
    exact indicator_of_notMem x.property _

/-- The actual compactly restricted pullback is L2 for the coordinate
metric wherever its native density agrees with the original metric. -/
theorem memLp_chart_indicator_native (g : RiemannianMetric 3 M)
    (gE : RiemannianMetric 3 E) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : MeasurableSet K) (hKs : K ⊆ e.source)
    (hρ : ∀ x ∈ K, gE.pullbackVolumeDensity id x = g.pullbackVolumeDensity e x)
    {φ : M → ℝ} (hφ : Measurable φ) (hf : MemLp φ 2 g.volumeMeasure) :
    MemLp (K.indicator (φ ∘ e)) 2 gE.volumeMeasure := by
  apply (memLp_indicator_iff_restrict hK).mpr
  have hmeasure : gE.volumeMeasure.restrict K =
      (volume.withDensity (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))).restrict K := by
    rw [native_volume_eq_density, restrict_withDensity hK, restrict_withDensity hK]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hK] with x hx
    exact congrArg ENNReal.ofReal (hρ x hx)
  rw [hmeasure]
  exact (memLp_pullback_density_of_measurable g e he hei hφ hf).mono_measure
    (Measure.restrict_mono hKs le_rfl)

#print axioms integral_mul_coordinateExtension_eq_density_measurable
#print axioms integral_mul_coordinateExtension_eq_native_measurable
#print axioms memLp_pullback_density_of_measurable
#print axioms measurable_chart_indicator
#print axioms memLp_chart_indicator_native

end Yamabe3.Parametrix
