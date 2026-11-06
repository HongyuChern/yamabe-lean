import Yamabe3.Analysis.BubbleLowWronskian
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-! Genuine compensated exterior low-mode Cauchy solver. The coefficient
is constructed from the actual source moment and positive fixed Gram mass.
The field is constructed by the past inverse plus the regular Jacobi mode. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction CompactlySupported
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

def bubbleWeightedCompensation (i:AngularIndex):ℝ →ᵇ ℝ:=
  (show C_c(ℝ,ℝ) from
    { toFun:=fun s=>Real.exp (2*s)*bubbleCompensation i (-s)
      continuous_toFun:=(Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        ((bubbleCompensation_smooth_compact i).1.continuous.comp continuous_neg)
      hasCompactSupport':=((bubbleCompensation_smooth_compact i).2.comp_homeomorph
        (Homeomorph.neg ℝ)).mul_left }).toBoundedContinuousFunction

theorem bubbleWeightedCompensation_identity (i:AngularIndex) (t:ℝ):
    Real.exp (2*t)*bubbleWeightedCompensation i (-t)=bubbleCompensation i t:=by
  change Real.exp (2*t)*(Real.exp (2*(-t))*bubbleCompensation i (-(-t)))=_
  rw [neg_neg,←mul_assoc,←Real.exp_add,show 2*t+2*(-t)=0 by ring,Real.exp_zero,one_mul]

def bubbleLowSourceMoment (i:AngularIndex) (H:ℝ →ᵇ ℝ) (t₀:ℝ):ℝ:=
  ∫t in Iic t₀,bubbleLowJacobi i t*(Real.exp (2*t)*H (-t))

def bubbleLowCompensatedSource (i:AngularIndex) (H:ℝ →ᵇ ℝ) (c:ℝ):ℝ →ᵇ ℝ:=
  H+c • bubbleWeightedCompensation i

theorem bubbleLowCompensatedSource_identity (i:AngularIndex) (H:ℝ →ᵇ ℝ) (c t:ℝ):
    Real.exp (2*t)*bubbleLowCompensatedSource i H c (-t)=
      Real.exp (2*t)*H (-t)+c*bubbleCompensation i t:=by
  change Real.exp (2*t)*(H (-t)+c*bubbleWeightedCompensation i (-t))=_
  rw [mul_add,←mul_assoc,mul_comm (Real.exp (2*t)) c,mul_assoc,bubbleWeightedCompensation_identity]

theorem bubbleLowCompensatedSource_moment (i:AngularIndex) (H:ℝ →ᵇ ℝ) (c:ℝ)
    {t₀:ℝ} (ht:0≤t₀):
    bubbleLowSourceMoment i (bubbleLowCompensatedSource i H c) t₀=
      bubbleLowSourceMoment i H t₀+c*bubbleCompensationMass i:=by
  unfold bubbleLowSourceMoment
  simp_rw [bubbleLowCompensatedSource_identity,mul_add]
  have hc:IntegrableOn (fun t=>bubbleLowJacobi i t*(c*bubbleCompensation i t)) (Iic t₀):=
    (((bubbleLowJacobi_smooth i).continuous.mul
      (continuous_const.mul (bubbleCompensation_smooth_compact i).1.continuous)).integrable_of_hasCompactSupport
      (((bubbleCompensation_smooth_compact i).2.mul_left).mul_left)).integrableOn
  rw [integral_add (bubbleLowJacobi_source_integrable i H t₀) hc]
  congr 1
  rw [←bubbleCompensationMass_truncated i ht,←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun t=>by ring

private theorem affine_jacobi (i:AngularIndex) (hi:i∈nativeLowIndexFinset)
    (P g:ℝ→ℝ) (hP:ContDiff ℝ 2 P)
    (heq:∀t,deriv (deriv P) t-bubbleLowCoefficient i t*P t=g t) (a:ℝ):
    let z:=fun t=> -P t+a*bubbleLowJacobi i t
    ContDiff ℝ 2 z ∧
    (∀t,deriv z t= -deriv P t+a*deriv (bubbleLowJacobi i) t) ∧
    ∀t,deriv (deriv z) t-bubbleLowCoefficient i t*z t= -g t:=by
  dsimp only
  have hZ:ContDiff ℝ 2 (bubbleLowJacobi i):=(bubbleLowJacobi_smooth i).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hd (t:ℝ):HasDerivAt (fun s=> -P s+a*bubbleLowJacobi i s)
      (-deriv P t+a*deriv (bubbleLowJacobi i) t) t:=
    ((hP.differentiable (by norm_num) t).hasDerivAt.neg).add
      ((hZ.differentiable (by norm_num) t).hasDerivAt.const_mul a)
  refine ⟨hP.neg.add (contDiff_const.mul hZ),fun t=>(hd t).deriv,?_⟩
  intro t
  rw [show deriv (fun s=> -P s+a*bubbleLowJacobi i s)=fun s=>
    -deriv P s+a*deriv (bubbleLowJacobi i) s from funext fun s=>(hd s).deriv]
  have hdd:deriv (fun s=> -deriv P s+a*deriv (bubbleLowJacobi i) s) t=
      -deriv (deriv P) t+a*deriv (deriv (bubbleLowJacobi i)) t:=by
    convert ((hP.differentiable_deriv_two t).hasDerivAt.neg.add
      ((hZ.differentiable_deriv_two t).hasDerivAt.const_mul a)).deriv using 1
    congr 1
  rw [hdd]
  have hz:=bubbleLowJacobi_equation i hi t
  have hp:=heq t
  unfold bubbleLowCoefficient at *
  linear_combination -hp + a * hz

/-- Both actual entrance data are attained, with no Cauchy compatibility
assumed. The compensating source and solution are constructed together. -/
theorem exists_actual_bubble_low_cauchy_solver (i:AngularIndex) (hi:i∈nativeLowIndexFinset)
    (H:ℝ →ᵇ ℝ) {t₀:ℝ} (ht:0<t₀) (d n:ℝ):
    ∃c:ℝ,∃z:ℝ→ℝ,
      c=bubbleLowCauchyCompensation i t₀ d n (bubbleLowSourceMoment i H t₀) ∧
      ContDiff ℝ 2 z ∧
      (∀t,deriv (deriv z) t-bubbleLowCoefficient i t*z t=
        -(Real.exp (2*t)*H (-t)+c*bubbleCompensation i t)) ∧
      z t₀=d ∧ deriv z t₀=n ∧
      Tendsto z atBot (𝓝 0) ∧ Tendsto (deriv z) atBot (𝓝 0):=by
  let c:=bubbleLowCauchyCompensation i t₀ d n (bubbleLowSourceMoment i H t₀)
  let Hc:=bubbleLowCompensatedSource i H c
  let P:=bubbleLowPastField i hi Hc
  let a:=(d+P t₀)/bubbleLowJacobi i t₀
  let z:=fun t=> -P t+a*bubbleLowJacobi i t
  have hP:=bubbleLowPastField_C2_equation i hi Hc
  have hz:=affine_jacobi i hi P _ hP.1 hP.2 a
  dsimp only at hz
  have hne:=bubbleLowJacobi_entrance_ne_zero i ht
  have hav:a*bubbleLowJacobi i t₀=d+P t₀:=by dsimp only [a];field_simp
  have hw:=bubbleLowPastField_wronskian i hi Hc t₀
  change bubbleLowWronskian i P t₀=bubbleLowSourceMoment i Hc t₀ at hw
  rw [bubbleLowCompensatedSource_moment i H c ht.le] at hw
  have hc:=bubbleLowCauchyCompensation_equation i t₀ d n (bubbleLowSourceMoment i H t₀)
  change bubbleCompensationMass i*c=_ at hc
  have hd:z t₀=d:=by dsimp only [z];linarith
  have hn:deriv z t₀=n:=by
    rw [hz.2.1]
    unfold bubbleLowWronskian at hw
    apply (mul_left_cancel₀ hne)
    linear_combination -hw -hc + deriv (bubbleLowJacobi i) t₀ * hav
  refine ⟨c,z,rfl,hz.1,?_,hd,hn,?_,?_⟩
  · intro t
    rw [hz.2.2,bubbleLowCompensatedSource_identity]
  · have hPbot:=bubbleLowPastField_bot i hi Hc
    have hZbot:=bubbleLowJacobi_bot i
    change Tendsto (fun t=> -P t+a*bubbleLowJacobi i t) atBot (𝓝 0)
    simpa using hPbot.1.neg.add (hZbot.1.const_mul a)
  · rw [show deriv z=fun t=> -deriv P t+a*deriv (bubbleLowJacobi i) t from funext hz.2.1]
    simpa using (bubbleLowPastField_bot i hi Hc).2.neg.add
      ((bubbleLowJacobi_bot i).2.const_mul a)

#print axioms bubbleWeightedCompensation_identity
#print axioms bubbleLowCompensatedSource_moment
#print axioms exists_actual_bubble_low_cauchy_solver
end Yamabe3.Analysis.Delaunay
