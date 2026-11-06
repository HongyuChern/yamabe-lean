import Yamabe3.Analysis.NativeOuterClassWindowExtension

/-! The ACTUAL auxiliary outer field has physical support strictly
inside the chart radius. The enclosing radius is chosen from the fixed
outer cutoff, not from an unrelated field or a pointwise sphere value. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic

 theorem nativeOuterAuxiliary_physical_support
    {v χ:E→ℝ} {a S:ℝ} (ha:0<a)
    (hsχ:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    (hz:∀x:E,χ (Real.exp S • x)=0→v x=0):
    tsupport (fun y:E=>v (a⁻¹ • y))⊆ball (0:E) (a*Real.exp ((1/8:ℝ)-S)):=by
  have hv:tsupport v⊆tsupport (fun x:E=>χ (Real.exp S • x)):=by
    apply closure_mono
    intro x hx
    exact fun hχ=>hx (hz x hχ)
  intro y hy
  have hyv:a⁻¹ • y∈tsupport v:=(tsupport_comp_eq_preimage v
    (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne'))).le hy
  have hn:=mem_ball_zero_iff.mp (nativeScaledCutoff_support hsχ S (hv hyv))
  rw [←Real.exp_add] at hn
  have hnorm:a*‖a⁻¹ • y‖=‖y‖:=by
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le,←mul_assoc,mul_inv_cancel₀ ha.ne',one_mul]
  apply mem_ball_zero_iff.mpr
  rw [←hnorm]
  exact mul_lt_mul_of_pos_left (by simpa only [sub_eq_add_neg] using hn) ha

 theorem nativeOuterAuxiliary_retained_support_radius
    {v χ:E→ℝ} {a S R:ℝ} {N:ℕ} (ha:0<a)
    (hsχ:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    (hz:∀x:E,χ (Real.exp S • x)=0→v x=0)
    (hcover:-S+1/2<(N:ℝ)/2) (hfit:a*Real.exp ((N:ℝ)/2+1)≤R):
    0<a*Real.exp ((1/4:ℝ)-S) ∧ a*Real.exp ((1/4:ℝ)-S)<R ∧
      tsupport (fun y:E=>v (a⁻¹ • y))⊆closedBall (0:E) (a*Real.exp ((1/4:ℝ)-S)):=by
  have hrad:a*Real.exp ((1/8:ℝ)-S)<a*Real.exp ((1/4:ℝ)-S):=
    mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by linarith)) ha
  refine ⟨mul_pos ha (Real.exp_pos _),?_,?_⟩
  · exact (mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by linarith:(1/4:ℝ)-S<(N:ℝ)/2+1)) ha).trans_le hfit
  · exact (nativeOuterAuxiliary_physical_support ha hsχ hz).trans
      ((ball_subset_ball hrad.le).trans ball_subset_closedBall)

#print axioms nativeOuterAuxiliary_physical_support
#print axioms nativeOuterAuxiliary_retained_support_radius
end Yamabe3.Analysis.SpherePolar
