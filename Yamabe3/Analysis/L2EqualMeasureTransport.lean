import Yamabe3.Analysis.L2ZeroExtension

/-! Exact change of measure identity, with no re-selection of an L2
function. The equality transport preserves norm and the actual AE class. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace Yamabe3.Analysis
variable {X:Type*} [MeasurableSpace X] {μ ν:Measure X}

def l2EqualMeasureCLM (h:μ=ν) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν := by
  subst ν
  exact ContinuousLinearMap.id ℝ _

theorem l2EqualMeasureCLM_ae (h:μ=ν) (U:Lp ℝ 2 μ) :
    (l2EqualMeasureCLM h U:X→ℝ)=ᵐ[ν](U:X→ℝ) := by
  subst ν
  exact ae_eq_rfl

theorem l2EqualMeasureCLM_norm_apply (h:μ=ν) (U:Lp ℝ 2 μ) :
    ‖l2EqualMeasureCLM h U‖=‖U‖ := by
  subst ν
  rfl

#print axioms l2EqualMeasureCLM_ae
#print axioms l2EqualMeasureCLM_norm_apply
end Yamabe3.Analysis
