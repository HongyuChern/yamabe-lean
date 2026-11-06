import Yamabe3.Analysis.NativeSupportedOuterNewtonRate
import Yamabe3.Analysis.NativeSupportedOuterValueDecay

/-! Actual r^(-1) whole-field value decay, in the existing weighted
collar normalization exp(3s/2) u(exp(-s)x), hence exp(5s/2). -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic

theorem exists_nativeSupportedOuter_Newton_value_decay (b:ℝ) {τ:ℝ} (ht:0<τ) :
    ∃C:ℝ,0≤C ∧ ∀(F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2)
      (σ:AngularH1) (hσ:NativeAngularSpectralRegular (3/2) (angularEmbedding σ)),
      (∀ᵐt:ℝ ∂volume,t<b→F t=0)→∀s:ℝ,s≤-τ-(1/2:ℝ)→
      ‖(nativeSupportedOuterAllScaleJet b ht F d n σ hσ s).val.1‖≤
        C*Real.exp (5*s/2)*(‖(F,(d,n))‖+‖σ‖) := by
  obtain ⟨C,hC,hbound⟩:=exists_nativeSupportedOuterCurve_Newton_rate b ht
  refine ⟨Real.sqrt (Real.exp 1)*(C*Real.exp (1/4)),by positivity,fun F d n σ hσ hF s hs=>?_⟩
  obtain ⟨w,hw,_,ha,hj⟩:=exists_nativeSupportedOuter_same_curve_all_scale b ht F d n σ hσ
  let U:=nativeSupportedOuterCurve b ht F d n σ
  let Us:ℝ→AngularL2:=fun t=>Real.exp (2*s) • U (t+s)
  have hUs:Continuous Us:=((nativeSupportedOuterCurve_continuous b ht F d n σ).comp
    (continuous_id.add_const s)).const_smul (Real.exp (2*s))
  have hr:=weightedCylinderShift_representation s ha
  have hb':∀t∈Icc (-(1/2:ℝ)) (1/2),‖Us t‖≤Real.exp (5*s/2)*(C*Real.exp (1/4)*(‖(F,(d,n))‖+‖σ‖)):=by
    intro t ht'
    change ‖Real.exp (2*s) • U (t+s)‖≤_
    rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
    have hh := hbound F d n σ hF (t+s) (by linarith only [ht'.2,hs])
    calc
      _ ≤ Real.exp (2*s)*(C*(‖(F,(d,n))‖+‖σ‖)*Real.exp ((t+s)/2)) :=
        mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
      _ = (C*(‖(F,(d,n))‖+‖σ‖))*Real.exp (2*s+(t+s)/2) := by rw [Real.exp_add];ring
      _ ≤ (C*(‖(F,(d,n))‖+‖σ‖))*Real.exp (5*s/2+1/4) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [ht'.2])) (by positivity)
      _ = _ := by rw [Real.exp_add];ring
  have hJ:((nativeSupportedOuterAllScaleJet b ht F d n σ hσ s).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      cylinderLift (weightedCylinderShift s w):=by
    filter_upwards [(hj s).1] with x hx
    exact hx.trans (cylinderLift_weightedCylinderShift s w x).symm
  have h:=native_bounded_angular_collar_norm hUs (weightedCylinderShift_measurable s hw) hr
    (by positivity:0≤Real.exp (5*s/2)*(C*Real.exp (1/4)*(‖(F,(d,n))‖+‖σ‖))) hb' _ hJ
  exact h.trans_eq (by ring)

#print axioms exists_nativeSupportedOuter_Newton_value_decay
end Yamabe3.Analysis.SpherePolar
