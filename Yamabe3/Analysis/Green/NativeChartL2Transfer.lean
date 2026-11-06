import Yamabe3.Analysis.Green.NativeSingularL2

/-!
# L2 transport from an actual coordinate metric to the original metric

The two actual densities need agree only on the support of the function.
This is the transfer required by a compactly supported parametrix residual
constructed for the global Euclidean extension of a native chart metric.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace Yamabe3.Parametrix

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- Genuine L2 membership transfers through the zero extension when the
actual coordinate densities agree on the function's support. -/
theorem memLp_coordinateExtension_of_native (g : RiemannianMetric 3 M)
    (gE : RiemannianMetric 3 E) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {f : E → ℝ} (hf : MemLp f 2 gE.volumeMeasure)
    (hρ : ∀ x ∈ tsupport f,
      gE.pullbackVolumeDensity id x = g.pullbackVolumeDensity e x) :
    MemLp (coordinateExtension e f) 2 g.volumeMeasure := by
  have hvE : gE.volumeMeasure = volume.withDensity
      (fun x => ENNReal.ofReal (gE.pullbackVolumeDensity id x)) := by
    have h := gE.map_restrict_volumeMeasure_symm (OpenPartialHomeomorph.refl E)
      contMDiffOn_id contMDiffOn_id
    simpa using h
  let μ := volume.withDensity (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))
  have hmeas : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have hμ : μ.restrict (tsupport f) = gE.volumeMeasure.restrict (tsupport f) := by
    rw [hvE]
    dsimp only [μ]
    rw [restrict_withDensity hmeas, restrict_withDensity hmeas]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hmeas] with x hx
    exact congrArg ENNReal.ofReal (hρ x hx).symm
  have hlocal : MemLp f 2 (μ.restrict (tsupport f)) := by
    rw [hμ]
    exact hf.restrict _
  have hi := (memLp_indicator_iff_restrict hmeas).mpr hlocal
  have hglobal : MemLp f 2 μ := by
    convert! hi using 1
    ext x
    by_cases hx : x ∈ tsupport f
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
  exact memLp_coordinateExtension_of_density g e he hei (hglobal.restrict e.source)

end Yamabe3.Parametrix
