import Yamabe3.Analysis.BubbleLowCompensation
import Yamabe3.Analysis.NativeLowC2Coefficients
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Actual low exterior particular solutions from the proved future
inverse after time reflection. The input is a bounded continuous weighted
source; the actual source is exp(2t) H(-t). No solution is an input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

def bubbleLowCoefficient (i:AngularIndex) (t:ℝ):ℝ:=
  1/4+angularEigenvalue i-(15/4)*fullBubbleDensity t

theorem bubbleLowCoefficient_bound (i:AngularIndex) (hi:i∈nativeLowIndexFinset) (t:ℝ):
    |bubbleLowCoefficient i t|≤7/2:=by
  have hlo:=(mem_nativeLowIndexFinset i).mp hi
  have hb:=fullBubbleDensity_bounds t
  rcases angularEigenvalue_zero_two_or_ge_six i with h0|h2|h6
  · unfold bubbleLowCoefficient
    rw [h0,abs_le]
    constructor <;> linarith
  · unfold bubbleLowCoefficient
    rw [h2,abs_le]
    constructor <;> linarith
  · exact (not_lt_of_ge h6 hlo).elim

def bubbleLowReflectedCoefficient (i:AngularIndex) (hi:i∈nativeLowIndexFinset):ℝ →ᵇ ℝ:=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun s=>bubbleLowCoefficient i (-s))
    (continuous_const.sub (continuous_const.mul (fullBubbleDensity_continuous.comp continuous_neg)))
    (7/2) (fun s=>by simpa only [Real.norm_eq_abs] using bubbleLowCoefficient_bound i hi (-s))

theorem bubbleLowReflectedCoefficient_norm (i:AngularIndex) (hi:i∈nativeLowIndexFinset):
    ‖bubbleLowReflectedCoefficient i hi‖≤7/2:=by
  apply (BoundedContinuousFunction.norm_le (by norm_num : (0:ℝ)≤7/2)).mpr
  intro s
  change |bubbleLowCoefficient i (-s)|≤7/2
  exact bubbleLowCoefficient_bound i hi (-s)

def bubbleLowPastField (i:AngularIndex) (hi:i∈nativeLowIndexFinset) (H:ℝ →ᵇ ℝ) (t:ℝ):ℝ:=
  Real.exp (2*t)*futurePotentialInverse 2 (by norm_num) (bubbleLowReflectedCoefficient i hi)
    (by have h:=bubbleLowReflectedCoefficient_norm i hi;norm_num;nlinarith) H (-t)

private theorem weighted_future_C2 (a H:ℝ →ᵇ ℝ) (ha:‖a‖<(2:ℝ)^2):
    let U:=futurePotentialInverse 2 (by norm_num) a ha H
    ContDiff ℝ 2 (fun s=>Real.exp (-2*s)*U s) ∧
    ∀s,deriv (deriv (fun t=>Real.exp (-2*t)*U t)) s=
      a s*(Real.exp (-2*s)*U s)+Real.exp (-2*s)*H s:=by
  dsimp only
  let U:=futurePotentialInverse 2 (by norm_num) a ha H
  have he:=futurePotentialInverse_equation (by norm_num : (0:ℝ)<2) a ha H
  dsimp only at he
  have hC:ContDiff ℝ 2 (fun s=>U s):=by
    apply contDiff_two_of_continuous_second_deriv he.1 he.2.1
    rw [show deriv (deriv (fun s=>U s))=_ from funext he.2.2.2]
    exact (((continuous_const.mul he.2.1.continuous).sub
      (continuous_const.mul U.continuous)).add H.continuous).add (a.continuous.mul U.continuous)
  refine ⟨(Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul hC,?_⟩
  intro s
  rw [exponential_conjugate_second_deriv_C2 he.1 he.2.1,he.2.2.2]
  ring

theorem bubbleLowPastField_C2_equation (i:AngularIndex) (hi:i∈nativeLowIndexFinset) (H:ℝ →ᵇ ℝ):
    ContDiff ℝ 2 (bubbleLowPastField i hi H) ∧
    ∀t,deriv (deriv (bubbleLowPastField i hi H)) t-bubbleLowCoefficient i t*bubbleLowPastField i hi H t=
      Real.exp (2*t)*H (-t):=by
  let a:=bubbleLowReflectedCoefficient i hi
  have ha:‖a‖<(2:ℝ)^2:=by have h:=bubbleLowReflectedCoefficient_norm i hi;dsimp only [a];norm_num;nlinarith
  let U:=futurePotentialInverse 2 (by norm_num) a ha H
  let z:=fun s=>Real.exp (-2*s)*U s
  have he:=weighted_future_C2 a H ha
  dsimp only at he
  have hz: bubbleLowPastField i hi H=fun t=>z (-t):=by
    funext t
    simp only [bubbleLowPastField,z,neg_mul,mul_neg,neg_neg,U,a]
  rw [hz]
  refine ⟨he.1.comp contDiff_neg,?_⟩
  intro t
  have hfirst:deriv (fun s=>z (-s))=fun s=> -deriv z (-s):=funext fun s=>deriv_comp_neg z s
  rw [hfirst]
  change deriv (-(fun s=>deriv z (-s))) t - _ = _
  rw [deriv.neg,deriv_comp_neg,neg_neg,he.2]
  change bubbleLowCoefficient i (-(-t))*(Real.exp (-2*(-t))*U (-t))+
    Real.exp (-2*(-t))*H (-t)-bubbleLowCoefficient i t*(Real.exp (-2*(-t))*U (-t))=_
  simp only [neg_neg,neg_mul]
  ring

theorem bubbleLowPastField_bounds (i:AngularIndex) (hi:i∈nativeLowIndexFinset) (H:ℝ →ᵇ ℝ) (t:ℝ):
    |bubbleLowPastField i hi H t|≤2*‖H‖*Real.exp (2*t) ∧
    |deriv (bubbleLowPastField i hi H) t|≤4*‖H‖*Real.exp (2*t):=by
  let a:=bubbleLowReflectedCoefficient i hi
  have ha:‖a‖<(2:ℝ)^2:=by have h:=bubbleLowReflectedCoefficient_norm i hi;dsimp only [a];norm_num;nlinarith
  let U:=futurePotentialInverse 2 (by norm_num) a ha H
  have hd:0<(2:ℝ)^2-‖a‖:=sub_pos.mpr ha
  have hb:‖H‖/((2:ℝ)^2-‖a‖)≤2*‖H‖:=by
    apply (div_le_iff₀ hd).mpr
    have hm:=mul_le_mul_of_nonneg_left (bubbleLowReflectedCoefficient_norm i hi) (norm_nonneg H)
    dsimp only [a]
    nlinarith
  constructor
  · change |Real.exp (2*t)*U (-t)|≤_
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    have hUn:|U (-t)|≤2*‖H‖:=
      (U.norm_coe_le_norm (-t)).trans ((futurePotentialInverse_norm_le (by norm_num : (0:ℝ)<2) a ha H).trans hb)
    nlinarith [mul_le_mul_of_nonneg_left hUn (Real.exp_pos (2*t)).le]
  · have hz:bubbleLowPastField i hi H=fun s=>Real.exp (-2*(-s))*U (-s):=by
      funext s
      simp only [bubbleLowPastField,U,a,neg_mul,mul_neg,neg_neg]
    rw [hz]
    change |deriv (fun s=>(fun y=>Real.exp (-2*y)*U y) (-s)) t|≤_
    rw [deriv_comp_neg (fun y=>Real.exp (-2*y)*U y) t,abs_neg]
    have h:=futurePotentialInverse_weighted_deriv_bound (by norm_num : (0:ℝ)<2) a ha H (-t)
    have hcoef:2*‖H‖/((2:ℝ)^2-‖a‖)≤4*‖H‖:=by
      have hh:=mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤2)
      simpa only [mul_div_assoc] using (show 2*(‖H‖/((2:ℝ)^2-‖a‖))≤4*‖H‖ by nlinarith)
    apply h.trans
    simpa only [neg_mul,mul_neg,neg_neg] using mul_le_mul_of_nonneg_right hcoef (Real.exp_pos (2*t)).le

#print axioms bubbleLowCoefficient_bound
#print axioms bubbleLowPastField_C2_equation
#print axioms bubbleLowPastField_bounds
end Yamabe3.Analysis.Delaunay
