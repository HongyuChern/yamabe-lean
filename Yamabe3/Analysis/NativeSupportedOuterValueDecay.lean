import Yamabe3.Analysis.NativeSupportedOuterDecayField
import Yamabe3.Analysis.NativeBoundedAngularCollar

/-! A quantitative shrinking bound for the actual physical L2 value on
all far exterior collars. The same curve and jets are used throughout;
this is a value estimate, not yet a derivative or feedback estimate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay UniformElliptic

theorem nativeSupportedOuterCurve_continuous (b:ℝ) {τ:ℝ} (ht:0<τ)
    (F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2) (σ:AngularH1) :
    Continuous (nativeSupportedOuterCurve b ht F d n σ) := by
  unfold nativeSupportedOuterCurve nativeBubbleFullSupportedCurve
  exact ((((nativeConjugatedCurve_continuous _).add (nativeReverseConjugatedCurve_continuous _)).add
    (nativeLowCauchyCurve_continuous ht _)).sub (nativePoissonExteriorCurve_continuous _ _)).add
      (nativePoissonExteriorCurve_continuous _ _)

theorem exists_nativeSupportedOuter_value_decay (b:ℝ) {τ:ℝ} (ht:0<τ) :
    ∃C:ℝ,0≤C ∧ ∀(F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2)
      (σ:AngularH1) (hσ:NativeAngularSpectralRegular (3/2) (angularEmbedding σ)),
      (∀ᵐt:ℝ ∂volume,t<b→F t=0)→∀s:ℝ,s≤-(1/2:ℝ)→
      ‖(nativeSupportedOuterAllScaleJet b ht F d n σ hσ s).val.1‖≤
        C*Real.exp (2*s)*(‖(F,(d,n))‖+‖σ‖) := by
  obtain ⟨C,hC,hbound⟩:=exists_nativeSupportedOuterCurve_halfLine_bound b ht
  refine ⟨Real.sqrt (Real.exp 1)*C,mul_nonneg (Real.sqrt_nonneg _) hC,fun F d n σ hσ hF s hs=>?_⟩
  obtain ⟨w,hw,_,ha,hj⟩:=exists_nativeSupportedOuter_same_curve_all_scale b ht F d n σ hσ
  let U:=nativeSupportedOuterCurve b ht F d n σ
  let Us:ℝ→AngularL2:=fun t=>Real.exp (2*s) • U (t+s)
  have hUs:Continuous Us:=((nativeSupportedOuterCurve_continuous b ht F d n σ).comp
    (continuous_id.add_const s)).const_smul (Real.exp (2*s))
  have hr:=weightedCylinderShift_representation s ha
  have hb':∀t∈Icc (-(1/2:ℝ)) (1/2),‖Us t‖≤Real.exp (2*s)*(C*(‖(F,(d,n))‖+‖σ‖)):=by
    intro t ht'
    change ‖Real.exp (2*s) • U (t+s)‖≤_
    rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (hbound F d n σ hF (t+s) (by linarith only [ht'.2,hs])) (Real.exp_pos _).le
  have hJ:((nativeSupportedOuterAllScaleJet b ht F d n σ hσ s).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      cylinderLift (weightedCylinderShift s w):=by
    filter_upwards [(hj s).1] with x hx
    exact hx.trans (cylinderLift_weightedCylinderShift s w x).symm
  have h:=native_bounded_angular_collar_norm hUs (weightedCylinderShift_measurable s hw) hr
    (by positivity:0≤Real.exp (2*s)*(C*(‖(F,(d,n))‖+‖σ‖))) hb' _ hJ
  exact h.trans_eq (by ring)

#print axioms nativeSupportedOuterCurve_continuous
#print axioms exists_nativeSupportedOuter_value_decay
end Yamabe3.Analysis.SpherePolar
