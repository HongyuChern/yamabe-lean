import Yamabe3.Analysis.BubbleLowPastLimits

/-! The low Cauchy compatibility functional is the actual integrated
Wronskian of the constructed solution and the actual regular Jacobi field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

def bubbleLowWronskian (i:AngularIndex) (P:ℝ→ℝ) (t:ℝ):ℝ:=
  bubbleLowJacobi i t*deriv P t-deriv (bubbleLowJacobi i) t*P t

theorem bubbleLowWronskian_hasDerivAt (i:AngularIndex) (hi:i∈nativeLowIndexFinset)
    (P g:ℝ→ℝ) (hP:ContDiff ℝ 2 P)
    (heq:∀t,deriv (deriv P) t-bubbleLowCoefficient i t*P t=g t) (t:ℝ):
    HasDerivAt (bubbleLowWronskian i P) (bubbleLowJacobi i t*g t) t:=by
  have hZ:=bubbleLowJacobi_smooth i
  have hZ':=(contDiff_infty_iff_deriv.mp hZ).2
  have h:=(((hZ.differentiable (by simp) t).hasDerivAt).mul
    (hP.differentiable_deriv_two t).hasDerivAt).sub
    (((hZ'.differentiable (by simp) t).hasDerivAt).mul
      (hP.differentiable (by norm_num) t).hasDerivAt)
  apply h.congr_deriv
  have hz:=bubbleLowJacobi_equation i hi t
  have hp:=heq t
  unfold bubbleLowCoefficient at hp
  linear_combination (bubbleLowJacobi i t) * hp - P t * hz

theorem bubbleLowPastField_wronskian (i:AngularIndex) (hi:i∈nativeLowIndexFinset)
    (H:ℝ →ᵇ ℝ) (t₀:ℝ):
    bubbleLowWronskian i (bubbleLowPastField i hi H) t₀=
      ∫t in Iic t₀,bubbleLowJacobi i t*(Real.exp (2*t)*H (-t)):=by
  have hP:=bubbleLowPastField_C2_equation i hi H
  have hZbot:=bubbleLowJacobi_bot i
  have hPbot:=bubbleLowPastField_bot i hi H
  have hwbot:Tendsto (bubbleLowWronskian i (bubbleLowPastField i hi H)) atBot (𝓝 0):=by
    change Tendsto (fun t=>bubbleLowJacobi i t*deriv (bubbleLowPastField i hi H) t-
      deriv (bubbleLowJacobi i) t*bubbleLowPastField i hi H t) atBot (𝓝 0)
    simpa using (hZbot.1.mul hPbot.2).sub (hZbot.2.mul hPbot.1)
  have h:=integral_Iic_of_hasDerivAt_of_tendsto'
    (fun t (_:t∈Iic t₀)=>bubbleLowWronskian_hasDerivAt i hi _ _ hP.1 hP.2 t)
    (bubbleLowJacobi_source_integrable i H t₀) hwbot
  simpa only [sub_zero] using h.symm

#print axioms bubbleLowWronskian_hasDerivAt
#print axioms bubbleLowPastField_wronskian
end Yamabe3.Analysis.Delaunay
