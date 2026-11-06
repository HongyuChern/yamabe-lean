import Yamabe3.Analysis.HilbertTimeTesting
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Parseval under the genuine time integral

The bound is the product of the two Hilbert norms at each time. Compact
support of the test proves its integrability. This permits the spectral
sum under the integral without any interchange with a time supremum.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Pointwise absolute Parseval bound, proved by genuine lp Holder. -/
theorem hilbert_absolute_pair_bound (b : HilbertBasis ι ℝ H) (x y : H) :
    (Summable fun i => |inner ℝ (b i) x| * |inner ℝ (b i) y|) ∧
      (∑' i, |inner ℝ (b i) x| * |inner ℝ (b i) y|) ≤ ‖x‖ * ‖y‖ := by
  have h := lp.tsum_mul_le_mul_norm (p := 2) (q := 2)
    (by simpa using Real.HolderConjugate.two_two) (b.repr x) (b.repr y)
  simpa only [b.repr_apply_apply, Real.norm_eq_abs, LinearIsometryEquiv.norm_map] using h

theorem hasSum_time_integral_inner_coefficients [Countable ι]
    (b : HilbertBasis ι ℝ H) {P U : ℝ → H}
    (hP : Continuous P) (hc : HasCompactSupport P) (hU : Continuous U) :
    HasSum (fun i => ∫ t : ℝ, inner ℝ (b i) (P t) * inner ℝ (b i) (U t))
      (∫ t : ℝ, inner ℝ (P t) (U t)) := by
  let bound : ι → ℝ → ℝ := fun i t => |inner ℝ (b i) (P t)| * |inner ℝ (b i) (U t)|
  have hbi : Integrable (fun t : ℝ => ∑' i, bound i t) := by
    apply ((hP.norm.mul hU.norm).integrable_of_hasCompactSupport hc.norm.mul_right).mono'
    · apply Measurable.aestronglyMeasurable
      exact Measurable.tsum fun i =>
        (((innerSL ℝ (b i)).continuous.comp hP).abs.mul
          ((innerSL ℝ (b i)).continuous.comp hU).abs).measurable
    · apply Eventually.of_forall
      intro t
      rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun i => mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      exact (hilbert_absolute_pair_bound b (P t) (U t)).2
  apply hasSum_integral_of_dominated_convergence bound
  · intro i
    exact (((innerSL ℝ (b i)).continuous.comp hP).mul
      ((innerSL ℝ (b i)).continuous.comp hU)).aestronglyMeasurable
  · intro i
    apply Eventually.of_forall
    intro t
    simp only [bound, Real.norm_eq_abs, abs_mul, le_refl]
  · exact Eventually.of_forall fun t => (hilbert_absolute_pair_bound b (P t) (U t)).1
  · exact hbi
  · apply Eventually.of_forall
    intro t
    convert b.hasSum_inner_mul_inner (P t) (U t) using 1
    congr 1
    funext i
    rw [real_inner_comm (b i) (P t)]

end Yamabe3.Analysis.Delaunay
