import Yamabe3.Analysis.NativePhysicalShellCriticalTransport
import Yamabe3.Analysis.NativeCompactChartSource

/-! Literal support of the scaled physical shell source. It is zero
on the receiving ball when the shell is outside it. No source cutoff
radius is allowed to move an unrelated input support bound. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic

theorem nativePhysicalShellSource_support_bounds {a:ℝ} (ha:0<a) (s:ℝ) {x:E}
    (hx:Real.exp (s-Real.log a) • x ∈ nativeSourceShell) :
    a*Real.exp (-s-1/2) < ‖x‖ ∧ ‖x‖ < a*Real.exp (-s+1/2) := by
  have hb:Real.exp (-(1/2:ℝ)) < ‖Real.exp (s-Real.log a) • x‖ ∧
      ‖Real.exp (s-Real.log a) • x‖ < Real.exp (1/2:ℝ) :=
    (nativePolarTimeWindow_norm (1/2) _).mp (nativeSourceShell_subset_collar hx)
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le] at hb
  have hlo:Real.exp (s-Real.log a)*(a*Real.exp (-s-1/2))=Real.exp (-(1/2:ℝ)) := by
    calc
      _ = Real.exp (s-Real.log a)*(Real.exp (Real.log a)*Real.exp (-s-1/2)) := by rw [Real.exp_log ha]
      _ = _ := by rw [←Real.exp_add,←Real.exp_add];congr 1;ring
  have hhi:Real.exp (s-Real.log a)*(a*Real.exp (-s+1/2))=Real.exp (1/2:ℝ) := by
    calc
      _ = Real.exp (s-Real.log a)*(Real.exp (Real.log a)*Real.exp (-s+1/2)) := by rw [Real.exp_log ha]
      _ = _ := by rw [←Real.exp_add,←Real.exp_add];congr 1;ring
  rw [←hlo] at hb
  rw [←hhi] at hb
  exact ⟨(mul_lt_mul_iff_right₀ (Real.exp_pos _)).mp hb.1,(mul_lt_mul_iff_right₀ (Real.exp_pos _)).mp hb.2⟩

theorem nativePhysicalShellSource_zero_inner {a:ℝ} (ha:0<a) (s:ℝ) (U:NativeCollarL2)
    {L:ℝ} (hL:L ≤ Real.exp (-s-1/2)) {x:E} (hx:x∈closedBall (0:E) (a*L)) :
    nativePhysicalShellSource a s U x=0 := by
  apply nativePhysicalShellSource_zero_off
  intro hs
  have hn:‖x‖ ≤ a*L := by simpa only [mem_closedBall,dist_zero_right] using hx
  exact (not_lt_of_ge (hn.trans (mul_le_mul_of_nonneg_left hL ha.le)))
    (nativePhysicalShellSource_support_bounds ha s hs).1

theorem nativePhysicalShellSource_zero_outer {a:ℝ} (ha:0<a) (s:ℝ) (U:NativeCollarL2)
    {R:ℝ} (hR:a*Real.exp (-s+1/2) ≤ R) {x:E} (hx:x∉ball (0:E) R) :
    nativePhysicalShellSource a s U x=0 := by
  apply nativePhysicalShellSource_zero_off
  intro hs
  have hn:R ≤ ‖x‖ := by simpa only [mem_ball_zero_iff,not_lt] using hx
  exact (not_lt_of_ge (hR.trans hn)) (nativePhysicalShellSource_support_bounds ha s hs).2

#print axioms nativePhysicalShellSource_support_bounds
#print axioms nativePhysicalShellSource_zero_inner
#print axioms nativePhysicalShellSource_zero_outer
end Yamabe3.Analysis.SpherePolar
