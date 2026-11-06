import Yamabe3.Analysis.BubbleLowPastSolver

/-! Actual outer-end limits and integrability for the regular bubble
Jacobi modes and the constructed past particular fields. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

private theorem exp_bot {a:ℝ} (ha:0<a):
    Tendsto (fun t:ℝ=>Real.exp (a*t)) atBot (𝓝 0):=
  Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_pos ha).2 tendsto_id)

theorem bubbleExpPower_bot {a:ℝ} (ha:0<a) (b:ℝ):
    Tendsto (bubbleExpPower a b) atBot (𝓝 0):=by
  have he:=exp_bot (by norm_num : (0:ℝ)<2)
  have hp: Tendsto (fun t:ℝ=>(1+Real.exp (2*t))^b) atBot (𝓝 1):=by
    simpa only [add_zero,Real.one_rpow] using
      (tendsto_const_nhds.add he).rpow_const (p:=b) (Or.inl (by norm_num : (1:ℝ)+0≠0))
  change Tendsto (fun t=>Real.exp (a*t)*(1+Real.exp (2*t))^b) atBot (𝓝 0)
  simpa only [mul_one,zero_mul] using (exp_bot ha).mul hp

private theorem slope_bot (a b:ℝ):
    Tendsto (bubbleLogSlope a b) atBot (𝓝 a):=by
  have he:=exp_bot (by norm_num : (0:ℝ)<2)
  have h:=(tendsto_const_nhds (x:=a) (f:=atBot)).add ((he.const_mul (2*b)).div
    (tendsto_const_nhds.add he) (by norm_num : (1:ℝ)+0≠0))
  change Tendsto (fun t=>a+2*b*Real.exp (2*t)/(1+Real.exp (2*t))) atBot (𝓝 a)
  simpa only [mul_zero,add_zero,zero_div,Pi.add_apply,Pi.div_apply] using h

theorem bubbleLowJacobi_bot (i:AngularIndex):
    Tendsto (bubbleLowJacobi i) atBot (𝓝 0) ∧
    Tendsto (deriv (bubbleLowJacobi i)) atBot (𝓝 0):=by
  have he:=exp_bot (by norm_num : (0:ℝ)<2)
  have hp:=bubbleExpPower_bot (by norm_num : (0:ℝ)<1/2) (-3/2)
  have ht:=bubbleExpPower_bot (by norm_num : (0:ℝ)<3/2) (-3/2)
  unfold bubbleLowJacobi
  split_ifs
  · constructor
    · change Tendsto (fun t=>bubbleExpPower (1/2) (-3/2) t*(1-Real.exp (2*t))) atBot (𝓝 0)
      simpa only [zero_mul,sub_zero] using hp.mul (tendsto_const_nhds.sub he)
    · rw [show deriv bubbleLowRadial=fun t=>
        bubbleExpPower (1/2) (-3/2) t*bubbleLogSlope (1/2) (-3/2) t*(1-Real.exp (2*t))-
        2*bubbleExpPower (1/2) (-3/2) t*Real.exp (2*t) from
          funext fun t=>(bubbleLowRadial_hasDerivAt t).deriv]
      simpa using ((hp.mul (slope_bot (1/2) (-3/2))).mul (tendsto_const_nhds.sub he)).sub
        ((hp.const_mul 2).mul he)
  · refine ⟨ht,?_⟩
    change Tendsto (deriv (bubbleExpPower (3/2) (-3/2))) atBot (𝓝 0)
    rw [show deriv (bubbleExpPower (3/2) (-3/2))=fun t=>
      bubbleExpPower (3/2) (-3/2) t*bubbleLogSlope (3/2) (-3/2) t from
      funext fun t=>(bubbleExpPower_hasDerivAt _ _ t).deriv]
    simpa using ht.mul (slope_bot (3/2) (-3/2))

theorem bubbleLowPastField_bot (i:AngularIndex) (hi:i∈nativeLowIndexFinset) (H:ℝ →ᵇ ℝ):
    Tendsto (bubbleLowPastField i hi H) atBot (𝓝 0) ∧
    Tendsto (deriv (bubbleLowPastField i hi H)) atBot (𝓝 0):=by
  have he:=exp_bot (by norm_num : (0:ℝ)<2)
  constructor
  · apply squeeze_zero_norm' (Eventually.of_forall fun t=>(bubbleLowPastField_bounds i hi H t).1)
    simpa using he.const_mul (2*‖H‖)
  · apply squeeze_zero_norm' (Eventually.of_forall fun t=>(bubbleLowPastField_bounds i hi H t).2)
    simpa using he.const_mul (4*‖H‖)

private theorem power_source_integrable (a k:ℝ) (hak:0<a+k) (H:ℝ →ᵇ ℝ) (t₀:ℝ):
    IntegrableOn (fun t=>bubbleExpPower a (-3/2) t*(Real.exp (k*t)*H (-t))) (Iic t₀):=by
  apply ((integrableOn_exp_mul_Iic hak t₀).const_mul ‖H‖).mono'
    (((bubbleExpPower_smooth a (-3/2)).continuous.mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (H.continuous.comp continuous_neg))).aestronglyMeasurable.restrict)
  apply Eventually.of_forall
  intro t
  have hp:0≤(1+Real.exp (2*t))^(-3/2:ℝ):=Real.rpow_nonneg (by positivity) _
  have hb:(1+Real.exp (2*t))^(-3/2:ℝ)≤1:=
    Real.rpow_le_one_of_one_le_of_nonpos (by have h:=Real.exp_pos (2*t);linarith) (by norm_num)
  have hH:|H (-t)|≤‖H‖:=H.norm_coe_le_norm (-t)
  change |bubbleExpPower a (-3/2) t*(Real.exp (k*t)*H (-t))|≤_
  rw [abs_mul,abs_of_pos (bubbleExpPower_pos _ _ _),abs_mul,abs_of_pos (Real.exp_pos _)]
  have hn:0≤‖H‖:=norm_nonneg H
  have hpow: bubbleExpPower a (-3/2) t≤Real.exp (a*t):=by
    unfold bubbleExpPower
    exact mul_le_of_le_one_right (Real.exp_pos _).le hb
  calc
    _ ≤ Real.exp (a*t)*(Real.exp (k*t)*‖H‖):=
      mul_le_mul hpow (mul_le_mul_of_nonneg_left hH (Real.exp_pos _).le)
        (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) (Real.exp_pos _).le
    _ = ‖H‖*Real.exp ((a+k)*t):=by rw [add_mul,Real.exp_add];ring

theorem bubbleLowJacobi_source_integrable (i:AngularIndex) (H:ℝ →ᵇ ℝ) (t₀:ℝ):
    IntegrableOn (fun t=>bubbleLowJacobi i t*(Real.exp (2*t)*H (-t))) (Iic t₀):=by
  unfold bubbleLowJacobi
  split_ifs
  · have h:=(power_source_integrable (1/2) 2 (by norm_num) H t₀).sub
      (power_source_integrable (1/2) 4 (by norm_num) H t₀)
    apply h.congr
    exact Eventually.of_forall fun t=>by
      simp only [Pi.sub_apply,bubbleLowRadial]
      rw [show (4:ℝ)*t=2*t+2*t by ring,Real.exp_add]
      ring
  · exact power_source_integrable (3/2) 2 (by norm_num) H t₀

#print axioms bubbleLowJacobi_bot
#print axioms bubbleLowPastField_bot
#print axioms bubbleLowJacobi_source_integrable
end Yamabe3.Analysis.Delaunay
