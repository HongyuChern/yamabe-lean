import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite product jets from actual smooth germs

Only finite pointwise smoothness is assumed. The Leibniz estimate is
localized on an actual open neighborhood before applying the within-set
formula. In particular these estimates apply to rescaled Green functions
at points away from the pole without requiring global smoothness at zero.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000

open Set Filter
open scoped ContDiff Topology

namespace Yamabe3.Analysis.UniformElliptic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual finite-order product inequality at a point; global
smoothness is unnecessary. -/
theorem norm_iteratedFDeriv_mul_le_of_contDiffAt {f g : E → ℝ} {x : E} {n : ℕ}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
  obtain ⟨U, hU, hfU⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨V, hV, hgV⟩ := hg.contDiffOn le_rfl (by simp)
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp (inter_mem hU hV)
  have hfo : ContDiffOn ℝ n f O := hfU.mono (fun _ hx => (hOsub hx).1)
  have hgo : ContDiffOn ℝ n g O := hgV.mono (fun _ hx => (hOsub hx).2)
  have h := norm_iteratedFDerivWithin_mul_le hfo hgo hO.uniqueDiffOn hxO le_rfl
  simpa only [iteratedFDerivWithin_of_isOpen _ hO hxO] using h

/-- A common bound on the finite jets of two actual germs gives the
explicit product constant 2^k. -/
theorem norm_iteratedFDeriv_mul_le_of_local_jets
    {f g : E → ℝ} {x : E} {k : ℕ}
    (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfj : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    (hgj : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g x‖ ≤ B)
    {n : ℕ} (hn : n ≤ k) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ (2 : ℝ) ^ k * A * B := by
  have hnk : (n : ℕ∞ω) ≤ k := by exact_mod_cast hn
  have hc : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ :=
      norm_iteratedFDeriv_mul_le_of_contDiffAt (hf.of_le hnk) (hg.of_le hnk)
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hn
      have hsubk : n - i ≤ k := (Nat.sub_le n i).trans hn
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfj i hik) (Nat.cast_nonneg _))
        (hgj (n - i) hsubk) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2 : ℝ) ^ n * A * B := by rw [← Finset.sum_mul, ← Finset.sum_mul, hc]
    _ ≤ (2 : ℝ) ^ k * A * B := by gcongr <;> norm_num

/-- The genuine fourth power has explicit finite-jet bound (2^k)^3 A^4.
No free polynomial-control field is supplied. -/
theorem norm_iteratedFDeriv_fourthPower_le_of_local_jets
    {f : E → ℝ} {x : E} {k : ℕ} (hf : ContDiffAt ℝ k f x)
    {A : ℝ} (hA : 0 ≤ A)
    (hfj : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    {n : ℕ} (hn : n ≤ k) :
    ‖iteratedFDeriv ℝ n (fun y => f y ^ 4) x‖ ≤ ((2 : ℝ) ^ k) ^ 3 * A ^ 4 := by
  have htwo : ∀ i ≤ k,
      ‖iteratedFDeriv ℝ i (fun y => f y ^ 2) x‖ ≤ (2 : ℝ) ^ k * A * A := by
    intro i hi
    simpa only [pow_two] using
      norm_iteratedFDeriv_mul_le_of_local_jets hf hf hA hA hfj hfj hi
  have hbound := norm_iteratedFDeriv_mul_le_of_local_jets
    (hf.pow 2) (hf.pow 2) (by positivity : 0 ≤ (2 : ℝ) ^ k * A * A)
    (by positivity : 0 ≤ (2 : ℝ) ^ k * A * A) htwo htwo hn
  have heq : (fun y => f y ^ 2 * f y ^ 2) = (fun y => f y ^ 4) := by
    funext y
    ring
  rw [heq] at hbound
  convert hbound using 1 <;> ring

#print axioms norm_iteratedFDeriv_mul_le_of_contDiffAt
#print axioms norm_iteratedFDeriv_mul_le_of_local_jets
#print axioms norm_iteratedFDeriv_fourthPower_le_of_local_jets

end Yamabe3.Analysis.UniformElliptic
