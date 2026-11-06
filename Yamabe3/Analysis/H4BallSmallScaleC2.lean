import Yamabe3.Analysis.UniformElliptic.ThreeDimensionalH4Jets
import Yamabe3.Analysis.UniformElliptic.JetScaling

/-! Whole-ball H4 controls the same representative's two-jets on every
smaller entrance dilation, with no inverse power of the smaller radius. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_H4_ball_smallScale_C2_bound :
    ∃C:ℝ,0<C ∧ ∀u:E→ℝ,ContDiffOn ℝ ∞ u (ball (0:E) 3) →
      ∀r∈Icc (0:ℝ) (1/4),∀n≤2,∀x∈closedBall (0:E) 2,
      ‖iteratedFDeriv ℝ n (fun y=>u (r • y)) x‖≤
        C*(derivativeProfile 2 (ball (0:E) 1) 4 u).toReal := by
  have hVc:IsCompact (closure (ball (0:E) 1)):=by
    rw [closure_ball (0:E) (by norm_num:(1:ℝ)≠0)]
    exact isCompact_closedBall _ _
  have hVO:closure (ball (0:E) 1)⊆ball (0:E) 3:=by
    rw [closure_ball (0:E) (by norm_num:(1:ℝ)≠0)]
    exact closedBall_subset_ball (by norm_num)
  obtain ⟨C,hC,hb⟩:=exists_local_h4_sup_two_jet_bound_on_compact
    (isCompact_closedBall (0:E) (1/2)) isOpen_ball hVc isOpen_ball hVO
      (closedBall_subset_ball (by norm_num:(1/2:ℝ)<1))
  refine ⟨C,hC,fun u hu r hr n hn x hx=>?_⟩
  have hx2:‖x‖≤2:=by simpa using hx
  have hrx:r • x∈closedBall (0:E) (1/2):=by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg hr.1]
    nlinarith only [hx2,hr.1,hr.2,norm_nonneg x]
  have huj:=hb hu n hn (r • x) hrx
  by_cases hn0:n=0
  · subst n
    simpa only [norm_iteratedFDeriv_zero] using huj
  · have hmem:r • x∈ball (0:E) 3:=(closedBall_subset_ball (by norm_num:(1/2:ℝ)<3)) hrx
    have he:=norm_iteratedFDeriv_local_centered_dilation isOpen_ball hu n hn0 hr.1 0 x hmem
    simp only [sub_zero] at he
    rw [he]
    exact (mul_le_mul le_rfl huj (norm_nonneg _) (pow_nonneg hr.1 _)).trans
      (mul_le_of_le_one_left (mul_nonneg hC.le ENNReal.toReal_nonneg)
        (pow_le_one₀ hr.1 (hr.2.trans (by norm_num))))

#print axioms exists_H4_ball_smallScale_C2_bound
end Yamabe3.Analysis.UniformElliptic
