import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-! Finite-square energy control constructs the infinite Banach-space sum.
The constant precedes the finite set; no absolute summability of the vectors
is assumed. -/
noncomputable section
set_option autoImplicit false
open Filter Finset
open scoped Topology
namespace Yamabe3.Analysis

theorem summable_of_finite_square_energy
    {ι H : Type*} [NormedAddCommGroup H] [CompleteSpace H]
    {v : ι → H} {a : ι → ℝ} {C : ℝ}
    (ha : Summable a) (hC : 0 ≤ C)
    (hv : ∀ s : Finset ι, ‖∑ i ∈ s,v i‖^2 ≤ C*(∑ i ∈ s,a i)) :
    Summable v := by
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  have hδ : 0 < ε^2/(C+1) := div_pos (sq_pos_of_pos hε) (by linarith)
  obtain ⟨s,hs⟩ := summable_iff_vanishing_norm.mp ha _ hδ
  refine ⟨s,fun t ht => ?_⟩
  have htail : (∑ i ∈ t,a i) < ε^2/(C+1) :=
    (le_abs_self _).trans_lt (by simpa only [Real.norm_eq_abs] using hs t ht)
  have hmul := (lt_div_iff₀ (by linarith : 0 < C+1)).mp htail
  have hbd := hv t
  have hn := norm_nonneg (∑ i ∈ t,v i)
  by_cases hc : C=0
  · subst C
    nlinarith [sq_nonneg ‖∑ i ∈ t,v i‖]
  · have hcpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hc)
    have hnonneg : 0 ≤ ∑ i ∈ t,a i := by
      nlinarith [sq_nonneg ‖∑ i ∈ t,v i‖]
    nlinarith

#print axioms summable_of_finite_square_energy
end Yamabe3.Analysis
