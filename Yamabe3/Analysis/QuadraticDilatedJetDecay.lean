import Yamabe3.Analysis.LinearDilatedJetDecay

/-! A retained zero first jet gives a genuine quadratic dilation bound.
The constant precedes every radius, point and finite derivative order.
This is the quantitative density input required by regular low jets;
qualitative coefficient smallness alone does not supply this factor. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter Metric
open scoped ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_quadratic_rescaled_zero_jet_bound
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hf0 : f 0 = 0)
    (hdf0 : fderiv ℝ f 0 = 0) (k : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      ∀ n ≤ k, ∀ x ∈ closedBall (0:E) R,
        ‖iteratedFDeriv ℝ n (fun y => f (r • y)) x‖ ≤ C * r^2 := by
  classical
  have hb : ∀ n : Fin (k+3), ∃ C : ℝ,
      ∀ x ∈ closedBall (0:E) R, ‖iteratedFDeriv ℝ n.val f x‖ ≤ C := by
    intro n
    exact (isCompact_closedBall (0:E) R).exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn
  choose C hC using hb
  let L := 1 + ∑ n : Fin (k+3), max 0 (C n)
  have hsum : 0 ≤ ∑ n : Fin (k+3), max 0 (C n) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  have hL : 0 < L := by dsimp only [L]; linarith
  have hLb (n : ℕ) (hn : n ≤ k+2) (x : E) (hx : x ∈ closedBall (0:E) R) :
      ‖iteratedFDeriv ℝ n f x‖ ≤ L := by
    let j : Fin (k+3) := ⟨n, by omega⟩
    have hj := (hC j x hx).trans (le_max_right 0 (C j))
    have hs := Finset.single_le_sum
      (fun i _ => le_max_left (0:ℝ) (C i)) (Finset.mem_univ j)
    exact (hj.trans hs).trans (by dsimp only [L]; linarith)
  have hD (y : E) (hy : y ∈ closedBall (0:E) R) :
      ‖fderiv ℝ f y‖ ≤ L * ‖y‖ := by
    have hsecond (z : E) (hz : z ∈ closedBall (0:E) R) :
        ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ L := by
      rw [← norm_iteratedFDeriv_one (fderiv ℝ f), norm_iteratedFDeriv_fderiv]
      exact hLb 2 (by omega) z hz
    have hh := (convex_closedBall (0:E) R).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hf.fderiv_right (m:=1) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).differentiable (by norm_num) z)
      hsecond (mem_closedBall_self hR.le) hy
    simpa only [hdf0, sub_zero] using hh
  refine ⟨(R+1)^2*L, by positivity, fun r hr hr1 n hn x hx => ?_⟩
  have hxR : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hx
  have hyR : r • x ∈ closedBall (0:E) R := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hr]
    exact (mul_le_of_le_one_left (norm_nonneg x) hr1).trans hxR
  have hgrad : ‖fderiv ℝ f (r • x)‖ ≤ L * (r * R) := by
    apply (hD _ hyR).trans
    rw [norm_smul, Real.norm_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxR hr) hL.le
  rcases n with _ | n
  · rw [norm_iteratedFDeriv_zero]
    have hinner (y : E) (hy : y ∈ closedBall (0:E) ‖r • x‖) :
        ‖fderiv ℝ f y‖ ≤ L * ‖r • x‖ := by
      apply (hD y ((closedBall_subset_closedBall (by simpa only [mem_closedBall, dist_zero_right] using hyR)) hy)).trans
      exact mul_le_mul_of_nonneg_left
        (by simpa only [mem_closedBall, dist_zero_right] using hy) hL.le
    have hv := (convex_closedBall (0:E) ‖r • x‖).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hf.differentiable (by simp) y) hinner
      (mem_closedBall_self (norm_nonneg _))
      (show r • x ∈ closedBall (0:E) ‖r • x‖ by simp)
    rw [hf0, sub_zero, sub_zero, norm_smul, Real.norm_of_nonneg hr] at hv
    calc
      _ ≤ L * (r * ‖x‖) * (r * ‖x‖) := hv
      _ ≤ L * (r * R) * (r * R) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxR hr) hL.le
        · exact mul_le_mul_of_nonneg_left hxR hr
        · positivity
        · positivity
      _ ≤ (R+1)^2 * L * r^2 := by nlinarith [mul_nonneg (sq_nonneg r) hL.le]
  · rw [iteratedFDeriv_comp_const_smul r (hf.of_le (by exact_mod_cast le_top)),
      norm_smul, norm_pow, Real.norm_of_nonneg hr]
    rcases n with _ | n
    · rw [pow_one, norm_iteratedFDeriv_one]
      apply (mul_le_mul_of_nonneg_left hgrad hr).trans
      calc
        r*(L*(r*R)) = R*(L*r^2) := by ring
        _ ≤ (R+1)^2*(L*r^2) := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
        _ = _ := by ring
    · have hpow : r^(n+1+1) ≤ r^2 := by
        exact pow_le_pow_of_le_one hr hr1 (by omega)
      apply (mul_le_mul hpow (hLb _ (by omega) _ hyR) (norm_nonneg _) (sq_nonneg r)).trans
      calc
        r^2*L = 1*(L*r^2) := by ring
        _ ≤ (R+1)^2*(L*r^2) := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
        _ = _ := by ring

#print axioms exists_quadratic_rescaled_zero_jet_bound
end Yamabe3.Analysis.UniformElliptic
