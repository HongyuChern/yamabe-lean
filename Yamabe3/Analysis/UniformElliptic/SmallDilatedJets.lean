import Yamabe3.Analysis.UniformElliptic.JetScaling
import Yamabe3.Analysis.UniformElliptic.NativeScaledCoefficients

/-!
# Small finite jets of the same actual dilated coefficients

A smooth scalar function vanishing at the origin has arbitrarily small
finite jets after sufficiently small dilation on a fixed compact ball.
The zeroth order uses its actual continuity at zero, and every positive
order uses the exact dilation factor. A single radius works for a finite
family. Thus the result gives genuine coefficient smallness, rather than
merely bounded coefficient jets or a pointwise value limit.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open Set Filter Metric
open scoped ContDiff Topology

namespace Yamabe3.Analysis.UniformElliptic

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_small_rescaled_zero_jets
    {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (hzero : f 0 = 0)
    (k : ℕ) {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 ≤ r → r < δ →
      ∀ n ≤ k, ∀ z ∈ closedBall (0 : E3) R,
        ‖iteratedFDeriv ℝ n (fun y => f (r • y)) z‖ ≤ η := by
  classical
  have hvalue : ∀ᶠ x : E3 in 𝓝 0, ‖f x‖ < η := by
    have h := hf.continuous.continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds (f 0) hη)
    simpa only [mem_ball, hzero, dist_zero_right] using h
  obtain ⟨ρ, hρ, hρb⟩ := Metric.mem_nhds_iff.mp hvalue
  have hb : ∀ n : Fin (k + 1), ∃ C : ℝ, ∀ x ∈ closedBall (0 : E3) R,
      ‖iteratedFDeriv ℝ n.val f x‖ ≤ C := by
    intro n
    exact (isCompact_closedBall (0 : E3) R).exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn
  choose C hC using hb
  let L := 1 + ∑ n : Fin (k + 1), max 0 (C n)
  have hsum : 0 ≤ ∑ n : Fin (k + 1), max 0 (C n) :=
    Finset.sum_nonneg fun _ _ => le_max_left _ _
  have hL : 0 < L := by dsimp only [L]; linarith
  have hLb (n : ℕ) (hn : n ≤ k) (x : E3) (hx : x ∈ closedBall (0 : E3) R) :
      ‖iteratedFDeriv ℝ n f x‖ ≤ L := by
    let j : Fin (k + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
    have hj := (hC j x hx).trans (le_max_right 0 (C j))
    have hsumj := Finset.single_le_sum (fun t _ => le_max_left 0 (C t)) (Finset.mem_univ j)
    exact (hj.trans hsumj).trans (by dsimp only [L]; linarith)
  refine ⟨min 1 (min (η / L) (ρ / R)),
    lt_min (by norm_num) (lt_min (div_pos hη hL) (div_pos hρ hR)), ?_⟩
  intro r hr hrδ n hn z hz
  have hr1 : r ≤ 1 := (hrδ.trans_le (min_le_left _ _)).le
  have hrη : r * L < η := (lt_div_iff₀ hL).mp
    (hrδ.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hrρ : r * R < ρ := (lt_div_iff₀ hR).mp
    (hrδ.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hzR : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hrz : r • z ∈ closedBall (0 : E3) R := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hr]
    exact (mul_le_of_le_one_left (norm_nonneg z) hr1).trans hzR
  by_cases hn0 : n = 0
  · subst n
    rw [norm_iteratedFDeriv_zero]
    apply le_of_lt
    apply hρb
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left hzR hr).trans_lt hrρ
  · have hfn : ContDiff ℝ n f := hf.of_le (by exact_mod_cast le_top)
    rw [iteratedFDeriv_comp_const_smul r hfn, norm_smul, norm_pow,
      Real.norm_of_nonneg hr]
    exact (mul_le_mul (pow_le_of_le_one hr hr1 hn0) (hLb n hn (r • z) hrz)
      (norm_nonneg _) hr).trans hrη.le

theorem exists_small_finite_rescaled_zero_jets
    {ι : Type*} [Fintype ι] (f : ι → E3 → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hzero : ∀ i, f i 0 = 0)
    (k : ℕ) {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 ≤ r → r < δ →
      ∀ i : ι, ∀ n ≤ k, ∀ z ∈ closedBall (0 : E3) R,
        ‖iteratedFDeriv ℝ n (fun y => f i (r • y)) z‖ ≤ η := by
  choose d hd hbound using fun i => exists_small_rescaled_zero_jets (hf i) (hzero i) k hR hη
  have hevent : ∀ᶠ r : ℝ in 𝓝 0, ∀ i : ι, r < d i :=
    eventually_all.mpr fun i => Iio_mem_nhds (hd i)
  obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ i n hn z hz
  exact hbound i r hr (hδb (by
    simpa only [mem_ball, dist_zero_right, Real.norm_of_nonneg hr] using hrδ) i) n hn z hz

#print axioms exists_small_rescaled_zero_jets
#print axioms exists_small_finite_rescaled_zero_jets

end Yamabe3.Analysis.UniformElliptic
