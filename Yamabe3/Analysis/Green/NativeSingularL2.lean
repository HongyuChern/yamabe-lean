import Yamabe3.Analysis.Green.NativeCutoffParametrix
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.Coordinates
import Yamabe3.Analysis.Green.EuclideanResidual

/-!
# Native L2 membership of the actual cutoff Newton singularity

The coordinate density is computed from the actual metric and smooth chart.
Its boundedness on the cutoff support is proved by compactness. The map of
the original restricted volume under the inverse chart then transfers the
genuine weighted Euclidean L2 statement to the original manifold.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal

namespace Yamabe3.Parametrix

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet
open Yamabe3.Analysis.GreenParametrix

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- A reverse coordinate L2 transfer for the real zero extension. No
pointwise regularity of the L2 function is postulated. -/
theorem memLp_coordinateExtension_of_density (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target) {f : E → ℝ}
    (hf : MemLp f 2 ((volume.withDensity
      (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))).restrict e.source)) :
    MemLp (coordinateExtension e f) 2 g.volumeMeasure := by
  rw [← g.map_restrict_volumeMeasure_symm e he hei] at hf
  have hp := hf.comp_of_map (e.symm.continuousOn.aemeasurable e.open_target.measurableSet)
  have ht : MemLp (coordinateExtension e f) 2 (g.volumeMeasure.restrict e.target) := by
    apply MemLp.ae_eq (hf_Lp := hp)
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
    exact (coordinateExtension_apply e f hy).symm
  have hi := (memLp_indicator_iff_restrict e.open_target.measurableSet).mpr ht
  convert! hi using 1
  ext y
  by_cases hy : y ∈ e.target
  · simp only [indicator_of_mem hy]
  · simp only [coordinateExtension, indicator_of_notMem hy]

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] in
/-- The cutoff inverse-radius function is L2 for the actual chart density.
Only continuity on its compact support is needed and is derived here. -/
theorem memLp_cutoffSingular_nativeDensity (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source) :
    MemLp (cutoffSingular χ) 2
      (volume.withDensity (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))) := by
  have hD : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) (tsupport χ) := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds (hχ hx)))
      (hD.mfderiv_injective (hχ hx))).1.continuousAt.continuousWithinAt
  obtain ⟨A, hA⟩ := χ.hasCompactSupport.isCompact.exists_bound_of_continuousOn hρ
  have hlocal : MemLp (cutoffSingular χ) 2
      ((volume.restrict (ball (0 : E) χ.rOut)).withDensity
        (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))) := by
    apply memLp_withDensity_of_le_inv_norm (A := ENNReal.ofReal A) (C := 1) ENNReal.ofReal_ne_top
    · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      apply ENNReal.ofReal_le_ofReal
      apply (le_abs_self _).trans
      apply hA
      rw [χ.tsupport_eq]
      exact ball_subset_closedBall hx
    · exact (χ.continuous.measurable.mul measurable_norm.inv).aestronglyMeasurable
    · exact Eventually.of_forall (fun x => by
        unfold cutoffSingular
        rw [abs_mul, abs_of_nonneg χ.nonneg, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right χ.le_one (inv_nonneg.mpr (norm_nonneg x)))
  rw [← restrict_withDensity measurableSet_ball] at hlocal
  have hi := (memLp_indicator_iff_restrict measurableSet_ball).mpr hlocal
  convert! hi using 1
  ext x
  by_cases hx : x ∈ ball (0 : E) χ.rOut
  · simp only [indicator_of_mem hx]
  · have hz : χ x = 0 := by
      apply Function.notMem_support.mp
      simpa only [χ.support_eq] using hx
    simp only [cutoffSingular, hz, zero_mul, indicator_of_notMem hx]

/-- The explicit `χ/r` zero extension belongs to the actual manifold's
native L2 space, so it is legal in the transposed Green pairing. -/
theorem memLp_singular (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source) :
    MemLp (singular e χ) 2 g.volumeMeasure :=
  memLp_coordinateExtension_of_density g e he hei
    ((memLp_cutoffSingular_nativeDensity g e he hei χ hχ).restrict e.source)

end Yamabe3.Parametrix
