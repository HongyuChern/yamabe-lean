import Yamabe3.Analysis.L2BoundedScalarMultiplier

/-! Restriction by an actual measurable set inside one L2 space. This
bounded operator retains the indicator representative and has norm at
most one, without any finite-volume assumption. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Yamabe3.Analysis
variable {X:Type*} [MeasurableSpace X] {μ:Measure X} (O:Set X) (hO:MeasurableSet O)

private theorem indicatorOne_bound : ∀ᵐx∂μ,‖O.indicator (fun _=> (1:ℝ)) x‖ ≤ 1 := by
  apply Eventually.of_forall
  intro x
  by_cases hx:x∈O <;> simp [hx]

def l2SetIndicatorCLM : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  l2ScalarMulCLM (O.indicator (fun _=>(1:ℝ)))
    ((measurable_const.indicator hO).aestronglyMeasurable) 1 zero_le_one (indicatorOne_bound O)

theorem l2SetIndicatorCLM_ae (U:Lp ℝ 2 μ) :
    (l2SetIndicatorCLM O hO U:X→ℝ)=ᵐ[μ]O.indicator (U:X→ℝ) := by
  apply (l2ScalarMul_ae (O.indicator (fun _=>(1:ℝ)))
    ((measurable_const.indicator hO).aestronglyMeasurable) 1 zero_le_one (indicatorOne_bound O) U).trans
  apply Eventually.of_forall
  intro x
  by_cases hx:x∈O <;> simp [hx]

theorem l2SetIndicatorCLM_norm : ‖l2SetIndicatorCLM (μ:=μ) O hO‖ ≤ 1 := by
  apply (l2SetIndicatorCLM O hO).opNorm_le_bound zero_le_one
  exact l2ScalarMul_norm_le (O.indicator (fun _=>(1:ℝ)))
    ((measurable_const.indicator hO).aestronglyMeasurable) 1 zero_le_one (indicatorOne_bound O)

#print axioms l2SetIndicatorCLM_ae
#print axioms l2SetIndicatorCLM_norm
end Yamabe3.Analysis
