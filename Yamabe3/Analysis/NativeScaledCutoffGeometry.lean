import Yamabe3.Analysis.NativeCompletedChartScaling

/-! Actual support and chart-fit certificates for the same physical
cutoffs. All radius choices are made before applying the source map. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar

theorem nativeScaledCutoff_support {χ:E→ℝ} {R:ℝ}
    (hs:tsupport χ⊆ball (0:E) R) (s:ℝ) :
    tsupport (fun x:E=>χ (Real.exp s • x))⊆ball (0:E) (R*Real.exp (-s)) := by
  intro x hx
  have hm:Real.exp s • x∈tsupport χ :=
    (tsupport_comp_eq_preimage χ (Homeomorph.smulOfNeZero (Real.exp s) (Real.exp_ne_zero _))).le hx
  have hb:=mem_ball_zero_iff.mp (hs hm)
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le] at hb
  have hh:=mul_lt_mul_of_pos_left hb (Real.exp_pos (-s))
  rw [←mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul] at hh
  exact mem_ball_zero_iff.mpr (by simpa only [mul_comm] using hh)

theorem euclideanDilatedBall_subset_closedBall {a r R:ℝ} (ha:0 < a) (har:a*r ≤ R) :
    euclideanDilatedDomain a (ball (0:E) r)⊆closedBall (0:E) R := by
  intro x hx
  have hh:‖a⁻¹ • x‖ < r:=mem_ball_zero_iff.mp hx
  rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le] at hh
  have hh':=mul_lt_mul_of_pos_left hh ha
  rw [←mul_assoc,mul_inv_cancel₀ ha.ne',one_mul] at hh'
  exact mem_closedBall.mpr (by simpa only [dist_zero_right] using hh'.le.trans har)

#print axioms nativeScaledCutoff_support
#print axioms euclideanDilatedBall_subset_closedBall
end Yamabe3.Analysis.SpherePolar
