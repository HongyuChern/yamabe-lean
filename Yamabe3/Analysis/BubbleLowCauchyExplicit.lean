import Yamabe3.Analysis.SecondOrderCauchyUniqueness
import Yamabe3.Analysis.NativeLowCauchyHalfLineBound
import Yamabe3.Analysis.BubbleLowJacobiFarRate

/-! Identify the SAME previously chosen compensated low Cauchy field
with the explicit past particular plus regular Jacobi solution.
No replacement of the chosen source or field is made. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

private theorem affineJacobi (i:AngularIndex) (hi:i∈nativeLowIndexFinset)
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

theorem bubbleLowZeroCauchyLinear_eq_explicit (i : AngularIndex) (hi : i∈nativeLowIndexFinset)
    {τ : ℝ} (ht : 0 < τ) (d n : ℝ) :
    let c := bubbleLowCauchyCompensation i τ d n 0
    let Hc := bubbleLowCompensatedSource i (0 : ℝ →ᵇ ℝ) c
    let P := bubbleLowPastField i hi Hc
    bubbleLowZeroCauchyLinear i hi ht (d,n) =
      fun t => -P t+((d+P τ)/bubbleLowJacobi i τ)*bubbleLowJacobi i t := by
  dsimp only
  let c := bubbleLowCauchyCompensation i τ d n 0
  let Hc := bubbleLowCompensatedSource i (0 : ℝ →ᵇ ℝ) c
  let P := bubbleLowPastField i hi Hc
  let a := (d+P τ)/bubbleLowJacobi i τ
  let z := fun t => -P t+a*bubbleLowJacobi i t
  let q := bubbleLowZeroCauchyLinear i hi ht (d,n)
  have hP := bubbleLowPastField_C2_equation i hi Hc
  have hz := affineJacobi i hi P _ hP.1 hP.2 a
  dsimp only at hz
  have hne := bubbleLowJacobi_entrance_ne_zero i ht
  have hav : a*bubbleLowJacobi i τ=d+P τ := by dsimp only [a];field_simp
  have hw := bubbleLowPastField_wronskian i hi Hc τ
  change bubbleLowWronskian i P τ=bubbleLowSourceMoment i Hc τ at hw
  have hm : bubbleLowSourceMoment i (0 : ℝ →ᵇ ℝ) τ=0 := by simp [bubbleLowSourceMoment]
  rw [bubbleLowCompensatedSource_moment i (0 : ℝ →ᵇ ℝ) c ht.le,hm,zero_add] at hw
  have hc := bubbleLowCauchyCompensation_equation i τ d n 0
  change bubbleCompensationMass i*c=_ at hc
  have hd : z τ=d := by dsimp only [z];linarith
  have hn : deriv z τ=n := by
    rw [hz.2.1]
    unfold bubbleLowWronskian at hw
    apply (mul_left_cancel₀ hne)
    linear_combination -hw -hc+deriv (bubbleLowJacobi i) τ*hav
  have hq := bubbleLowZeroCauchyLinear_spec i hi ht d n
  change ContDiff ℝ 2 q ∧ _ at hq
  have hez : ∀t,deriv (deriv z) t-bubbleLowCoefficient i t*z t= -c*bubbleCompensation i t := by
    intro t
    have hh := hz.2.2 t
    dsimp only [Hc] at hh
    rw [bubbleLowCompensatedSource_identity] at hh
    simpa using hh
  exact secondOrderCauchy_eq_of_bounded_coefficient (bubbleLowCoefficient i)
    (fun t => -c*bubbleCompensation i t) q z (by norm_num : (0 : ℝ) ≤ 7/2)
    (bubbleLowCoefficient_bound i hi) hq.1 hz.1 hq.2.1 hez
    (hq.2.2.1.trans hd.symm) (hq.2.2.2.1.trans hn.symm)

#print axioms bubbleLowZeroCauchyLinear_eq_explicit
end Yamabe3.Analysis.Delaunay
