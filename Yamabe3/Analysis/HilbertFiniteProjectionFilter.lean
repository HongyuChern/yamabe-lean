import Yamabe3.Analysis.HilbertFiniteProjection
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Logic.Equiv.List

/-!
# Actual finite Hilbert projection limits along countably generated filters

The original Hilbert-basis sum converges along the full finite-set filter.
Composing with any actual cofinal family gives the same pointwise limit.
The proved uniform projection bound provides one integrable dominating
function, so the filter form of dominated convergence gives the actual
compact-time square-error limit.  In particular a countable basis gives
the full Finset net, not merely a selected exhaustion sequence.
-/

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace Yamabe3.Analysis.Delaunay

variable {H ι J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem finiteHilbertProjection_tendsto_filter
    (b : HilbertBasis ι ℝ H) {l : Filter J} {s : J → Finset ι}
    (hs : Tendsto s l atTop) (x : H) :
    Tendsto (fun j => finiteHilbertProjection b (s j) x) l (𝓝 x) := by
  have h : HasSum (fun i => inner ℝ (b i) x • b i) x := by
    simpa only [HilbertBasis.repr_apply_apply] using b.hasSum_repr x
  exact h.comp hs

theorem finiteHilbertProjection_integral_error_tendsto_filter
    (b : HilbertBasis ι ℝ H) {l : Filter J} [l.IsCountablyGenerated]
    {s : J → Finset ι} (hs : Tendsto s l atTop)
    {U : ℝ → H} (hU : Continuous U) (a c : ℝ) :
    Tendsto (fun j => ∫ t in Icc a c, ‖finiteHilbertProjection b (s j) (U t) - U t‖ ^ 2)
      l (𝓝 0) := by
  have hbound : Integrable (fun t : ℝ => 4 * ‖U t‖ ^ 2) (volume.restrict (Icc a c)) := by
    convert ((hU.norm.pow 2).const_mul 4).integrableOn_Icc (μ := volume) (a := a) (b := c)
      using 1 <;> rfl
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Icc a c)) (l := l) (fun t : ℝ => 4 * ‖U t‖ ^ 2)
    (F := fun j t => ‖finiteHilbertProjection b (s j) (U t) - U t‖ ^ 2)
    (f := fun _ => (0 : ℝ))
    (Eventually.of_forall fun j =>
      ((((continuous_finiteHilbertProjection b (s j)).comp hU).sub hU).norm.pow 2).aestronglyMeasurable)
    (Eventually.of_forall fun j => Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact finiteHilbertProjection_sub_norm_sq_le b (s j) (U t))
    hbound
    (Eventually.of_forall fun t => by
      simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
        ((finiteHilbertProjection_tendsto_filter b hs (U t)).sub
          (tendsto_const_nhds (x := U t))).norm.pow 2)
  simpa only [integral_zero] using h

/-- This is a genuine full finite-set net statement. Countability is
used to justify the filter DCT, rather than to select a subsequence. -/
theorem finiteHilbertProjection_integral_error_tendsto_finset
    [Countable ι] (b : HilbertBasis ι ℝ H) {U : ℝ → H}
    (hU : Continuous U) (a c : ℝ) :
    Tendsto (fun s : Finset ι => ∫ t in Icc a c,
      ‖finiteHilbertProjection b s (U t) - U t‖ ^ 2) atTop (𝓝 0) :=
  finiteHilbertProjection_integral_error_tendsto_filter b tendsto_id hU a c

#print axioms finiteHilbertProjection_tendsto_filter
#print axioms finiteHilbertProjection_integral_error_tendsto_filter
#print axioms finiteHilbertProjection_integral_error_tendsto_finset

end Yamabe3.Analysis.Delaunay
