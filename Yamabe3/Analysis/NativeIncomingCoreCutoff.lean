import Yamabe3.Analysis.H4GraphCompactC1Realization

/-! A fixed puncture gate for the actual incoming field. It kills that
field on a neighborhood of the true interface r=1 and retains it outside
the fixed ball of radius 3. The range bound is kept for source estimates. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar

theorem exists_nativeIncoming_core_cutoff :
    ∃χ:E→ℝ,ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ⊆ball (0:E) 3 ∧
      (∀x:E,0 ≤ χ x ∧ χ x ≤ 1) ∧
      ∀x∈closedBall (0:E) 2,χ=ᶠ[𝓝 x](fun _=>1) := by
  obtain ⟨χ,hχ,hc,hs,hr,h1⟩:=PoincareMT.exists_contMDiff_cutoff_of_isCompact (n:=3)
    (isCompact_closedBall (0:E) 2) isOpen_ball (closedBall_subset_ball (by norm_num:(2:ℝ) < 3))
  exact ⟨χ,hχ.contDiff,hc,hs,hr,h1⟩

theorem nativeIncoming_gate_zero_near_interface
    {χ:E→ℝ} (h1:∀x∈closedBall (0:E) 2,χ=ᶠ[𝓝 x](fun _=>1))
    (u:E→ℝ) {x:E} (hx:‖x‖=1) :
    (fun y:E=>(1-χ y)*u y)=ᶠ[𝓝 x](fun _=>0) := by
  have hx2:x∈closedBall (0:E) 2 := by rw [mem_closedBall,dist_zero_right,hx];norm_num
  filter_upwards [h1 x hx2] with y hy
  simp only [hy,sub_self,zero_mul]

#print axioms exists_nativeIncoming_core_cutoff
#print axioms nativeIncoming_gate_zero_near_interface
end Yamabe3.Analysis.SpherePolar
