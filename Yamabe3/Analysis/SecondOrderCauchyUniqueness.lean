import Yamabe3.Analysis.BubbleLowCauchySolver
import Mathlib.Analysis.ODE.ExistUnique

/-! Literal Cauchy uniqueness for the bounded-coefficient scalar ODE.
This will identify the already chosen low field with its explicit
past-particular-plus-Jacobi formula before sharpening its far rate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter
open scoped Topology ContDiff NNReal
namespace Yamabe3.Analysis.Delaunay

theorem secondOrderCauchy_eq_of_bounded_coefficient
    (a p q z : ℝ → ℝ) {A t₀ : ℝ} (hA : 0 ≤ A) (ha : ∀t, |a t| ≤ A)
    (hq : ContDiff ℝ 2 q) (hz : ContDiff ℝ 2 z)
    (heq : ∀t, deriv (deriv q) t-a t*q t=p t)
    (hez : ∀t, deriv (deriv z) t-a t*z t=p t)
    (hvalue : q t₀=z t₀) (hderiv : deriv q t₀=deriv z t₀) : q=z := by
  let K : ℝ≥0 := ⟨max 1 A, le_trans (by norm_num) (le_max_left _ _)⟩
  let v : ℝ → (ℝ×ℝ) → (ℝ×ℝ) := fun t X => (X.2,a t*X.1+p t)
  have hv : ∀t, LipschitzOnWith K (v t) (univ : Set (ℝ×ℝ)) := by
    intro t
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro X Y
    rw [dist_eq_norm,dist_eq_norm]
    change ‖(X.2-Y.2,a t*X.1+p t-(a t*Y.1+p t))‖ ≤ _
    rw [Prod.norm_def]
    apply max_le
    · have hh : ‖X.2-Y.2‖ ≤ ‖X-Y‖ := by exact le_max_right _ _
      apply hh.trans
      have hmon := mul_le_mul_of_nonneg_right (le_max_left 1 A) (norm_nonneg (X-Y))
      simp only [one_mul] at hmon
      convert! hmon using 1
    · have hid : a t*X.1+p t-(a t*Y.1+p t)=a t*(X.1-Y.1) := by ring
      rw [hid,norm_mul,Real.norm_eq_abs]
      have hh : ‖X.1-Y.1‖ ≤ ‖X-Y‖ := by exact le_max_left _ _
      exact (mul_le_mul (ha t) hh (norm_nonneg _) hA).trans
        (mul_le_mul_of_nonneg_right (le_max_right 1 A) (norm_nonneg (X-Y)))
  have hf : ∀t, HasDerivAt (fun s => (q s,deriv q s)) (v t (q t,deriv q t)) t ∧
      (q t,deriv q t)∈(univ : Set (ℝ×ℝ)) := by
    intro t
    refine ⟨?_,mem_univ _⟩
    have ht := ((hq.differentiable (by norm_num) t).hasDerivAt).prodMk
      (hq.differentiable_deriv_two t).hasDerivAt
    have hid : deriv (deriv q) t=a t*q t+p t := by linarith [heq t]
    simpa only [hid,v] using ht
  have hg : ∀t, HasDerivAt (fun s => (z s,deriv z s)) (v t (z t,deriv z t)) t ∧
      (z t,deriv z t)∈(univ : Set (ℝ×ℝ)) := by
    intro t
    refine ⟨?_,mem_univ _⟩
    have ht := ((hz.differentiable (by norm_num) t).hasDerivAt).prodMk
      (hz.differentiable_deriv_two t).hasDerivAt
    have hid : deriv (deriv z) t=a t*z t+p t := by linarith [hez t]
    simpa only [hid,v] using ht
  have hh := ODE_solution_unique_univ hv hf hg (Prod.ext hvalue hderiv)
  exact congrArg (fun f : ℝ → (ℝ×ℝ) => fun t => (f t).1) hh

#print axioms secondOrderCauchy_eq_of_bounded_coefficient
end Yamabe3.Analysis.Delaunay
