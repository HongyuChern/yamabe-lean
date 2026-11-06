import Yamabe3.Analysis.NativeSupportedOuterTailCorrection
import Yamabe3.Analysis.PhysicalCutoffSourceSupport

/-! The same physical bubble tail vanishes on its literal inner ball.
This is needed before using homogeneous receiving estimates after
tail absorption. No volume AE identity is restricted to a sphere. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M : Type*} [TopologicalSpace M]

theorem fullBubbleScaledTail_zero_inner (τ c a : ℝ) (ha : 0 < a) (x : E)
    (hx : ‖x‖ ≤ a*Real.exp c) : fullBubbleScaledTail τ c (Real.log a) x=0 := by
  have hn : ‖Real.exp (-Real.log a) • x‖ ≤ Real.exp c := by
    rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      _ ≤ Real.exp (-Real.log a)*(a*Real.exp c) := mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le
      _ = _ := by rw [Real.exp_neg,Real.exp_log ha,← mul_assoc,inv_mul_cancel₀ ha.ne',one_mul]
  simp only [fullBubbleScaledTail,fullBubblePotentialTail,indicator,mem_setOf_eq,
    if_neg (not_lt_of_ge hn),mul_zero]

theorem native_physicalBubbleTail_zero_inner
    (e : OpenPartialHomeomorph E M) (K : Set E) (τ c a : ℝ) (ha : 0 < a)
    {R : ℝ} (hR : R ≤ a*Real.exp c) (hsource : ball (0 : E) R ⊆ e.source) :
    ∀y∈e '' ball (0 : E) R,
      nativeCompactChartFunction e K (fullBubbleScaledTail τ c (Real.log a)) y=0 := by
  rintro y ⟨x,hx,rfl⟩
  have hxsource := hsource hx
  have htail : fullBubbleScaledTail τ c (Real.log a) x=0 :=
    fullBubbleScaledTail_zero_inner τ c a ha x ((mem_ball_zero_iff.mp hx).le.trans hR)
  rw [nativeCompactChartFunction,coordinateExtension_comp_apply e _ hxsource]
  by_cases hK : x∈K
  · rw [indicator_of_mem hK,htail]
  · rw [indicator_of_notMem hK]

#print axioms fullBubbleScaledTail_zero_inner
#print axioms native_physicalBubbleTail_zero_inner
end Yamabe3.Analysis.SpherePolar
