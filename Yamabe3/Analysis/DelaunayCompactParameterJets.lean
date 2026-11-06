import Yamabe3.Analysis.DelaunayAnnularPotentialJets

/-! Actual spatial jet bounds on a compact state/coordinate product.
The coefficient family is represented by the same complete smooth state
flow. Compactness is applied to joint jets, not separately to each orbit. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter Metric
open scoped ContDiff Topology
namespace Yamabe3.Analysis.Delaunay
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem joint_state_local_spatial_jet_smooth {O : Set E3} {F : DelaunayState × E3 → ℝ}
    (hF : ∀ q : DelaunayState × E3, q.2 ∈ O → ContDiffAt ℝ ∞ F q)
    (n : ℕ) (q : DelaunayState × E3) (hq : q.2 ∈ O) :
    ContDiffAt ℝ ∞ (fun p : DelaunayState × E3 =>
      iteratedFDeriv ℝ n (fun x => F (p.1, x)) p.2) q := by
  induction n generalizing q with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def] using!
      (hF q hq).continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ E3 ℝ).symm : _ →L[ℝ] E3 [×0]→L[ℝ] ℝ)
  | succ n ih =>
    have hh : ContDiffAt ℝ ∞
        (Function.uncurry (fun p : DelaunayState × E3 =>
          iteratedFDeriv ℝ n (fun x => F (p.1, x)))) (q, q.2) := by
      exact (ih (q.1, q.2) hq).comp (q, q.2)
        (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞ (fun p : DelaunayState × E3 =>
        fderiv ℝ (iteratedFDeriv ℝ n (fun x => F (p.1, x))) p.2) q :=
      hh.fderiv contDiffAt_snd (by simp)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def] using!
      hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E3) ℝ).symm :
          _ →L[ℝ] E3 [×(n + 1)]→L[ℝ] ℝ)

theorem exists_state_compact_spatial_jet_bound {O K : Set E3}
    (hK : IsCompact K) (hKO : K ⊆ O) {F : DelaunayState × E3 → ℝ}
    (hF : ∀ q : DelaunayState × E3, q.2 ∈ O → ContDiffAt ℝ ∞ F q) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : DelaunayState, ‖s‖ ≤ 2 →
      ∀ n ≤ k, ∀ x ∈ K, ‖iteratedFDeriv ℝ n (fun y => F (s,y)) x‖ ≤ C := by
  have hj (n : ℕ) : ∃ C : ℝ, ∀ p ∈ closedBall (0 : DelaunayState) 2 ×ˢ K,
      ‖iteratedFDeriv ℝ n (fun x => F (p.1,x)) p.2‖ ≤ C := by
    apply ((isCompact_closedBall (0 : DelaunayState) 2).prod hK).exists_bound_of_continuousOn
    intro p hp
    exact (joint_state_local_spatial_jet_smooth hF n p (hKO hp.2)).continuousAt.continuousWithinAt
  choose C hC using hj
  refine ⟨∑ n ∈ Finset.range (k+1), max 0 (C n),
    Finset.sum_nonneg (fun _ _ => le_max_left _ _), ?_⟩
  intro s hs n hn x hx
  have hsB : s ∈ closedBall (0 : DelaunayState) 2 := by
    simpa only [mem_closedBall, dist_zero_right] using hs
  exact ((hC n (s,x) ⟨hsB,hx⟩).trans (le_max_right _ _)).trans
    (Finset.single_le_sum (fun _ _ => le_max_left _ _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))

#print axioms exists_state_compact_spatial_jet_bound
end Yamabe3.Analysis.Delaunay
