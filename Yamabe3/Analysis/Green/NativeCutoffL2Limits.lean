import Yamabe3.Analysis.Green.NativeSingularL2

/-!
# Native transposed integral limit for the cutoff singularity

The domination is the actual L1 product of an arbitrary native L2 test with
the constructed native L2 singularity. No boundedness or global coordinate
extension of the test is required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace Yamabe3.Parametrix

open PoincareMT

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- The explicit positive regularization converges in every native L2
pairing, by actual volume dominated convergence. -/
theorem tendsto_integral_mul_regularized (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source)
    {f : M → ℝ} (hf : MemLp f 2 g.volumeMeasure) :
    Tendsto (fun ε : ℝ => ∫ y, f y * regularized e χ ε y ∂g.volumeMeasure)
      (𝓝[>] 0) (𝓝 (∫ y, f y * singular e χ y ∂g.volumeMeasure)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun y => ‖f y‖ * singular e χ y)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hf.aestronglyMeasurable.mul
      (contMDiff_regularized e hei χ hχ hε).continuous.aestronglyMeasurable
  · apply Eventually.of_forall
    intro ε
    filter_upwards [regularized_le_singular_ae g e χ ε] with y hy
    calc
      ‖f y * regularized e χ ε y‖ = ‖f y‖ * regularized e χ ε y := by
        rw [norm_mul, Real.norm_of_nonneg (regularized_nonneg e χ ε y)]
      _ ≤ ‖f y‖ * singular e χ y := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
  · exact hf.norm.integrable_mul (memLp_singular g e he hei χ hχ)
  · filter_upwards [tendsto_regularized_ae g e χ] with y hy
    exact tendsto_const_nhds.mul (hy.mono_left nhdsWithin_le_nhds)

end Yamabe3.Parametrix
