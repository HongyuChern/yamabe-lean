import Yamabe3.Analysis.UniformElliptic.SmallDilatedJets
import Mathlib.Analysis.Calculus.MeanValue

/-! A quantitative radius factor for actual smooth coefficients vanishing
at the pole. Unlike qualitative smallness, this factor can pay the sum
of errors over infinitely many shrinking collars. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter Metric
open scoped ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_linear_rescaled_zero_jet_bound
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hf0 : f 0=0)
    (k : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ,0 < C ∧ ∀ r : ℝ,0 ≤ r → r ≤ 1 →
      ∀ n ≤ k,∀ x ∈ closedBall (0:E) R,
        ‖iteratedFDeriv ℝ n (fun y => f (r • y)) x‖ ≤ C*r := by
  classical
  have hb : ∀ n : Fin (k+2),∃ C : ℝ,∀ x ∈ closedBall (0:E) R,‖iteratedFDeriv ℝ n.val f x‖ ≤ C := by
    intro n
    exact (isCompact_closedBall (0:E) R).exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn
  choose C hC using hb
  let L := 1+∑ n : Fin (k+2),max 0 (C n)
  have hL : 0 < L := by
    have h : 0 ≤ ∑ n : Fin (k+2),max 0 (C n) := Finset.sum_nonneg (fun (n : Fin (k+2)) _ => le_max_left (0:ℝ) (C n))
    dsimp [L]
    linarith
  have hLb (n : ℕ) (hn : n ≤ k+1) (x : E) (hx : x ∈ closedBall (0:E) R) :
      ‖iteratedFDeriv ℝ n f x‖ ≤ L := by
    let j : Fin (k+2) := ⟨n,by omega⟩
    have hj := (hC j x hx).trans (le_max_right 0 (C j))
    have hsum := Finset.single_le_sum (fun (i : Fin (k+2)) _ => le_max_left (0:ℝ) (C i)) (Finset.mem_univ j)
    exact (hj.trans hsum).trans (by dsimp [L];linarith)
  refine ⟨(R+1)*L,by positivity,fun r hr hr1 n hn x hx => ?_⟩
  have hxR : ‖x‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hrx : r • x ∈ closedBall (0:E) R := by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg hr]
    exact (mul_le_of_le_one_left (norm_nonneg x) hr1).trans hxR
  by_cases hn0 : n=0
  · subst n
    rw [norm_iteratedFDeriv_zero]
    have hd : ∀ y ∈ closedBall (0:E) R,‖fderiv ℝ f y‖ ≤ L := by
      intro y hy
      simpa only [norm_iteratedFDeriv_one] using hLb 1 (by omega) y hy
    have h := (convex_closedBall (0:E) R).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hf.differentiable (by simp) y) hd (mem_closedBall_self hR.le) hrx
    rw [hf0,sub_zero,sub_zero,norm_smul,Real.norm_of_nonneg hr] at h
    calc
      _ ≤ L*(r*‖x‖) := h
      _ ≤ L*(r*R) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxR hr) hL.le
      _ ≤ (R+1)*L*r := by nlinarith [mul_nonneg hL.le hr]
  · rw [iteratedFDeriv_comp_const_smul r (hf.of_le (by exact_mod_cast le_top)),norm_smul,norm_pow,
      Real.norm_of_nonneg hr]
    calc
      _ ≤ r*L := mul_le_mul (pow_le_of_le_one hr hr1 hn0) (hLb n (by omega) (r • x) hrx) (norm_nonneg _) hr
      _ ≤ (R+1)*L*r := by nlinarith [mul_nonneg (mul_nonneg hR.le hL.le) hr]

theorem exists_linear_finite_rescaled_zero_jet_bound
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ)
    (hf : ∀ i,ContDiff ℝ ∞ (f i)) (hf0 : ∀ i,f i 0=0)
    (k : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ,0 < C ∧ ∀ r : ℝ,0 ≤ r → r ≤ 1 →
      ∀ i : ι,∀ n ≤ k,∀ x ∈ closedBall (0:E) R,
        ‖iteratedFDeriv ℝ n (fun y => f i (r • y)) x‖ ≤ C*r := by
  classical
  choose C hC hb using fun i => exists_linear_rescaled_zero_jet_bound (hf i) (hf0 i) k hR
  let L := 1+∑ i,C i
  have hsum : 0 ≤ ∑ i,C i := Finset.sum_nonneg (fun i _ => (hC i).le)
  refine ⟨L,by dsimp [L];linarith,fun r hr hr1 i n hn x hx => ?_⟩
  have hi := Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
  exact (hb i r hr hr1 n hn x hx).trans (mul_le_mul_of_nonneg_right
    (hi.trans (by dsimp [L];linarith)) hr)

#print axioms exists_linear_rescaled_zero_jet_bound
#print axioms exists_linear_finite_rescaled_zero_jet_bound
end Yamabe3.Analysis.UniformElliptic
