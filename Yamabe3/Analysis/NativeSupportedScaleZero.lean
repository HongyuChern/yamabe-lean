import Yamabe3.Analysis.NativeBubbleFullSupportedField
import Yamabe3.Analysis.NativeSupportedExteriorCauchy

/-! Scale-zero identities from the actual same-function representatives.
These identify the global constructions with their original entrance jets. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeBubbleParticularAllScaleJet_zero_eq (τ : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeBubbleParticularAllScaleJetCLM τ 0 F=
      nativeL2ParticularJetCLM (fullBubbleHighPotential τ) (fullBubblePhasePotential_plus_kernel τ) F := by
  obtain ⟨w,hw,hae,hj⟩ := nativeBubbleParticularAllScale_same_field τ F
  let P := fullBubbleHighPotential τ
  have ho := nativeL2ParticularValueCLM_eq_lift P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound
    (fullBubblePhasePotential_plus_kernel τ) F hw hae
  have h0 : ((nativeBubbleParticularAllScaleRawJetCLM τ 0 F).1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w := by
    simpa only [mul_zero,zero_div,neg_zero,Real.exp_zero,one_mul,one_smul] using hj 0
  apply nativeCollarJet_value_injective
  apply Lp.ext
  exact h0.trans ho.symm

theorem nativeLowReverseAllScaleJet_zero_eq (v : ℝ→ℝ) (hv : Continuous v)
    (hb : ∀t,0≤v t ∧ v t≤1) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeLowReverseAllScaleJetCLM v hv hb 0 F=nativeLowReverseL2JetCLM v hv hb F := by
  have h := nativeLowReverseAllScale_same_field v hv hb 0 F
  have h0 : ((nativeLowReverseAllScaleRawJetCLM v hv hb 0 F).1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      nativeLowReverseL2PhysicalField v hv hb F := by
    simpa only [mul_zero,zero_div,neg_zero,Real.exp_zero,one_mul,one_smul] using h
  apply nativeCollarJet_value_injective
  apply Lp.ext
  exact h0.trans (nativeLowReverseL2Value_same_field v hv hb F).symm

#print axioms nativeBubbleParticularAllScaleJet_zero_eq
#print axioms nativeLowReverseAllScaleJet_zero_eq
end Yamabe3.Analysis.SpherePolar
