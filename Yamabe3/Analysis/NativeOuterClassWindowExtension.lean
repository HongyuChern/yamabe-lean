import Yamabe3.Analysis.NativeOuterOperatorWindowExtension

/-! The same cutoff representative on the finite window determines
its class on the ENTIRE Euclidean exterior. Beyond the window the actual
cutoff is zero; no equation or representative is extrapolated. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic

 theorem nativeOuterCutoff_exterior_support_window
    {χ:E→ℝ} (hsχ:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    {S:ℝ} {N:ℕ} (hcover:-S+1/2<(N:ℝ)/2) {x:E}
    (hx:1<‖x‖) (hxχ:x∈tsupport (fun y:E=>χ (Real.exp S • y))):
    x∈nativePolarTimeWindow (Ioc (-(N:ℝ)/2) 0):=by
  have houter:‖x‖<Real.exp ((1/8:ℝ)-S):=by
    have hh:=mem_ball_zero_iff.mp (nativeScaledCutoff_support hsχ S hxχ)
    rw [←Real.exp_add] at hh
    simpa only [sub_eq_add_neg] using hh
  have hn:0<‖x‖:=by linarith
  have hl:=Real.log_lt_log hn houter
  rw [Real.log_exp] at hl
  have h0:=Real.log_nonneg hx.le
  exact ⟨norm_pos_iff.mp hn,by linarith,by linarith⟩

 theorem nativeOuterCutoff_window_class_extends
    {u v χ:E→ℝ} {S:ℝ} {N:ℕ}
    (hsχ:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ))) (hcover:-S+1/2<(N:ℝ)/2)
    (he:EqOn v (fun x=>χ (Real.exp S • x)*u x) (nativePolarTimeWindow (Ioc (-(N:ℝ)/2) 0)))
    (hz:∀x:E,χ (Real.exp S • x)=0→v x=0):
    EqOn v (fun x=>χ (Real.exp S • x)*u x) {x:E|1<‖x‖}:=by
  intro x hx
  change v x=χ (Real.exp S • x)*u x
  by_cases hχ:χ (Real.exp S • x)=0
  · rw [hz x hχ,hχ,zero_mul]
  · have hxχ:x∈tsupport (fun y:E=>χ (Real.exp S • y)):=
      subset_closure (show x∈Function.support (fun y:E=>χ (Real.exp S • y)) from hχ)
    exact he (nativeOuterCutoff_exterior_support_window hsχ hcover hx hxχ)

 theorem nativeOuterCutoff_realization_zero_off_chart
    {v χ:E→ℝ} {S a R:ℝ} {N:ℕ} (ha:0<a)
    (hsχ:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ))) (hcover:-S+1/2<(N:ℝ)/2)
    (hz:∀x:E,χ (Real.exp S • x)=0→v x=0)
    (hfit:a*Real.exp ((N:ℝ)/2+1)≤R):
    ∀x:E,x∉closedBall (0:E) R→v (a⁻¹ • x)=0:=by
  intro x hx
  apply hz
  by_contra hχ
  have hxχ:a⁻¹ • x∈tsupport (fun y:E=>χ (Real.exp S • y)):=
    subset_closure (show a⁻¹ • x∈Function.support (fun y:E=>χ (Real.exp S • y)) from hχ)
  have hn:‖a⁻¹ • x‖<Real.exp ((N:ℝ)/2+1):=by
    have hh:=mem_ball_zero_iff.mp (nativeScaledCutoff_support hsχ S hxχ)
    rw [←Real.exp_add] at hh
    exact hh.trans (Real.exp_lt_exp.mpr (by linarith))
  have hnorm:a*‖a⁻¹ • x‖=‖x‖:=by
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le,←mul_assoc,mul_inv_cancel₀ ha.ne',one_mul]
  apply hx
  rw [mem_closedBall_zero_iff]
  rw [←hnorm]
  exact (mul_le_mul_of_nonneg_left hn.le ha.le).trans hfit

#print axioms nativeOuterCutoff_exterior_support_window
#print axioms nativeOuterCutoff_window_class_extends
#print axioms nativeOuterCutoff_realization_zero_off_chart
end Yamabe3.Analysis.SpherePolar
