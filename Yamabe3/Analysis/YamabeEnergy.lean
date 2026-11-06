import Yamabe3.Target.Statement
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Tactic.Linarith

/-!
# The first energy implication of the actual Yamabe constant

The input is positivity of the quotient infimum defined in the target file.
Neither coercivity nor invertibility is placed in a structure. These results
concern smooth nonzero tests; extension to H1 and an operator inverse is OPEN.
-/

set_option autoImplicit false
open MeasureTheory
open scoped Manifold ContDiff

namespace Yamabe3.Target

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem yamabeConstant_le_quotient (g : PoincareMT.RiemannianMetric 3 M)
    (hY : 0 < yamabeConstant g) {v : M → ℝ}
    (hv : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ v) (hne : v ≠ 0) :
    yamabeConstant g ≤ quotient g v := by
  have hb : BddBelow {q : ℝ | ∃ v : M → ℝ,
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ v ∧ v ≠ 0 ∧ q = quotient g v} := by
    by_contra h
    have hz : yamabeConstant g = 0 := Real.sInf_of_not_bddBelow h
    exact (ne_of_gt hY) hz
  exact csInf_le hb ⟨v, hv, hne, rfl⟩

theorem critical_denominator_pos_of_yamabe_pos
    (g : PoincareMT.RiemannianMetric 3 M) (hY : 0 < yamabeConstant g)
    {v : M → ℝ} (hv : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ v) (hne : v ≠ 0) :
    0 < (∫ x, |v x| ^ 6 ∂g.volumeMeasure) ^ (1 / 3 : ℝ) := by
  have hq : 0 < quotient g v := hY.trans_le (yamabeConstant_le_quotient g hY hv hne)
  have hnonneg : 0 ≤ (∫ x, |v x| ^ 6 ∂g.volumeMeasure) ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg (integral_nonneg (fun x => pow_nonneg (abs_nonneg (v x)) 6)) _
  by_contra h
  have hz := le_antisymm (not_lt.mp h) hnonneg
  have hzero : quotient g v = 0 := by
    unfold quotient
    rw [hz, div_zero]
  rw [hzero] at hq
  exact (lt_irrefl 0) hq

/-- Genuine Yamabe inequality for each smooth nonzero test. This is not yet
an H1 coercivity or Green-function existence theorem. -/
theorem energy_lower_bound (g : PoincareMT.RiemannianMetric 3 M)
    (hY : 0 < yamabeConstant g) {v : M → ℝ}
    (hv : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ v) (hne : v ≠ 0) :
    yamabeConstant g * (∫ x, |v x| ^ 6 ∂g.volumeMeasure) ^ (1 / 3 : ℝ) ≤
      energy g v := by
  exact (le_div_iff₀ (critical_denominator_pos_of_yamabe_pos g hY hv hne)).mp
    (yamabeConstant_le_quotient g hY hv hne)

theorem energy_pos (g : PoincareMT.RiemannianMetric 3 M)
    (hY : 0 < yamabeConstant g) {v : M → ℝ}
    (hv : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ v) (hne : v ≠ 0) :
    0 < energy g v :=
  (mul_pos hY (critical_denominator_pos_of_yamabe_pos g hY hv hne)).trans_le
    (energy_lower_bound g hY hv hne)

#print axioms yamabeConstant_le_quotient
#print axioms critical_denominator_pos_of_yamabe_pos
#print axioms energy_lower_bound
#print axioms energy_pos

end Yamabe3.Target
