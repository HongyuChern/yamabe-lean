import PoincareLib.Topology.MetricSpace.Completeness
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Proper barriers and actual metric completeness

This is a general metric/topological module. It constructs no Yamabe solution.
The compact-background logarithmic sublevel lemma makes exclusion of zero-radius
points explicit. Applications must derive the actual distance-growth estimate.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Yamabe3.Topology

open Filter Set

/-- A proper real barrier that grows by at most intrinsic distance makes an
extended metric space complete. Only finite-distance pairs need the estimate.

For a punctured compact manifold, compactness of the barrier sublevels must be
proved by exclusion of the punctures, and the distance estimate must be proved
from the actual conformal metric. Neither input is asserted automatically. -/
theorem completeSpace_of_compact_barrier_sublevels
    {X : Type*} [PseudoEMetricSpace X] (b : X → ℝ)
    (hcompact : ∀ R : ℝ, IsCompact {x : X | b x ≤ R})
    (hgrowth : ∀ x y : X, edist x y ≠ ⊤ →
      b x ≤ b y + (edist x y).toReal) :
    CompleteSpace X := by
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff'.mp hu 1 zero_lt_one
  have htail : ∀ᶠ k in atTop, u k ∈ {x : X | b x ≤ b (u N) + 1} := by
    filter_upwards [eventually_ge_atTop N] with k hk
    have hdist : edist (u k) (u N) < (1 : ℝ≥0∞) := hN k hk
    have hfinite : edist (u k) (u N) ≠ ⊤ :=
      ne_top_of_lt hdist
    have hreal : (edist (u k) (u N)).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) hdist.le
    have hbound := hgrowth (u k) (u N) hfinite
    change b (u k) ≤ b (u N) + 1
    linarith
  obtain ⟨x, _, hx⟩ := (hcompact (b (u N) + 1)).isComplete (map u atTop) hu
    (le_principal_iff.mpr htail)
  exact ⟨x, hx⟩

end Yamabe3.Topology

namespace Yamabe3.Topology

open Set

/-- On the positive locus of a continuous real function on a compact space,
the negative logarithm has compact sublevels. In a punctured-manifold
application, the zero set of the chosen radius must equal the deleted set. -/
theorem isCompact_negative_log_sublevel
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (r : X → ℝ) (hr : Continuous r) (R : ℝ) :
    IsCompact {x : {x : X // 0 < r x} | -Real.log (r x) ≤ R} := by
  apply Subtype.isCompact_iff.mpr
  have heq :
      ((↑) '' {x : {x : X // 0 < r x} | -Real.log (r x) ≤ R} : Set X) =
        {x : X | Real.exp (-R) ≤ r x} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      apply (Real.le_log_iff_exp_le y.property).mp
      change -Real.log (r y) ≤ R at hy
      linarith
    · intro hx
      have hrx : 0 < r x := (Real.exp_pos (-R)).trans_le hx
      refine ⟨⟨x, hrx⟩, ?_, rfl⟩
      have hlog := (Real.le_log_iff_exp_le hrx).mpr hx
      change -Real.log (r x) ≤ R
      linarith
  rw [heq]
  exact (isClosed_le continuous_const hr).isCompact

end Yamabe3.Topology
