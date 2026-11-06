import Yamabe3.Analysis.UniformElliptic.SmallDilatedJets

/-! Smooth metric coefficients have uniform finite jets on dilated balls,
including the origin. No annular estimate is used across its excluded point. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter Metric
open scoped ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_smooth_dilation_ball_jets {f:E→ℝ} (hf:ContDiff ℝ ∞ f)
    (k:ℕ) {R:ℝ} (hR:0≤R) :
    ∃C:ℝ,0≤C ∧ ∀r∈Icc (0:ℝ) 1,∀n≤k,∀x∈closedBall (0:E) R,
      ‖iteratedFDeriv ℝ n (fun y=>f (r • y)) x‖≤C := by
  classical
  have hb:∀n:Fin (k+1),∃C:ℝ,∀x∈closedBall (0:E) R,‖iteratedFDeriv ℝ n.val f x‖≤C:=by
    intro n
    exact (isCompact_closedBall (0:E) R).exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn
  choose C hC using hb
  let B:=∑n:Fin (k+1),max 0 (C n)
  have hB:0≤B:=Finset.sum_nonneg (fun _ _=>le_max_left _ _)
  refine ⟨B,hB,fun r hr n hn x hx=>?_⟩
  have hrx:r • x∈closedBall (0:E) R:=by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg hr.1]
    exact (mul_le_of_le_one_left (norm_nonneg x) hr.2).trans (by simpa using hx)
  let j:Fin (k+1):=⟨n,Nat.lt_succ_of_le hn⟩
  have hj:‖iteratedFDeriv ℝ n f (r • x)‖≤B:=
    ((hC j _ hrx).trans (le_max_right 0 _)).trans
      (Finset.single_le_sum (fun _ _=>le_max_left 0 _) (Finset.mem_univ j))
  rw [iteratedFDeriv_comp_const_smul r (hf.of_le (by exact_mod_cast le_top)),norm_smul,norm_pow,
    Real.norm_of_nonneg hr.1]
  exact (mul_le_mul le_rfl hj (norm_nonneg _) (pow_nonneg hr.1 _)).trans
    (mul_le_of_le_one_left hB (pow_le_one₀ hr.1 hr.2))

#print axioms exists_smooth_dilation_ball_jets
end Yamabe3.Analysis.UniformElliptic
