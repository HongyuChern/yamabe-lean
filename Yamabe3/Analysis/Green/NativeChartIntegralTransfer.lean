import Yamabe3.Analysis.Green.NativeChartL2Transfer
import Yamabe3.Analysis.Green.NativeLocalParametrix

/-!
# Intrinsic integral transport for zero-extended chart functions

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
Only continuity of the native multiplier and measurability of the possibly
singular coordinate function are required. -/
theorem integral_mul_coordinateExtension_eq_density (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {f : E → ℝ} (hf : Measurable f) {φ : M → ℝ} (hφ : Continuous φ) :
    (∫ y, φ y * coordinateExtension e f y ∂g.volumeMeasure) =
      ∫ x in e.source, (φ (e x) * f x) * g.pullbackVolumeDensity e x := by
  have hmap := g.map_restrict_volumeMeasure_symm e he hei
  have hm : AEStronglyMeasurable (fun x => φ (e x) * f x)
      ((g.volumeMeasure.restrict e.target).map e.symm) := by
    rw [hmap]
    exact ((hφ.comp_continuousOn e.continuousOn).aestronglyMeasurable
      e.open_source.measurableSet).mul hf.aestronglyMeasurable
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
theorem integral_mul_coordinateExtension_eq_native (g : RiemannianMetric 3 M)
    (gE : RiemannianMetric 3 E) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {f : E → ℝ} (hf : Measurable f) (hfs : tsupport f ⊆ e.source)
    (hρ : ∀ x ∈ tsupport f,
      gE.pullbackVolumeDensity id x = g.pullbackVolumeDensity e x)
    {φ : M → ℝ} (hφ : Continuous φ) :
    (∫ y, φ y * coordinateExtension e f y ∂g.volumeMeasure) =
      ∫ x, φ (e x) * f x ∂gE.volumeMeasure := by
  rw [integral_mul_coordinateExtension_eq_density g e he hei hf hφ,
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

end Yamabe3.Parametrix
