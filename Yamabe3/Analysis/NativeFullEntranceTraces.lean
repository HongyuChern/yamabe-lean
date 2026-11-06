import Yamabe3.Analysis.NativeLowL2NormalTrace
import Yamabe3.Analysis.NativeFullDelaunayCollar
import Yamabe3.Analysis.NativeCollarJetValueInjective

/-! The full same-source field keeps its true low entrance and normal
trace. No zero trace is imposed on the low future inverse. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0≤v t ∧ v t≤1)

theorem nativeLowL2AllScaleJet_zero (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeLowL2AllScaleJetCLM v hv hb 0 F=nativeLowL2JetCLM v hv hb F := by
  apply nativeCollarJet_value_injective
  apply Lp.ext
  have hs := nativeLowL2AllScale_same_field v hv hb F 0
  have hs0 : ((nativeLowL2AllScaleRawJetCLM v hv hb 0 F).1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      nativeLowL2PhysicalField v hv hb F := by
    simpa only [mul_zero,zero_div,neg_zero,Real.exp_zero,one_mul,one_smul] using hs
  exact hs0.trans (nativeLowL2Value_same_field v hv hb F).symm

variable (P : NativeHighPotential)
  (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)

theorem nativeFullL2AllScaleJet_zero (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeFullL2AllScaleJetCLM P hp v hv hb 0 F=nativeL2HalfJetCLM P hp F+nativeLowL2JetCLM v hv hb F := by
  change nativeL2HalfAllScaleJetCLM P hp 0 F+nativeLowL2AllScaleJetCLM v hv hb 0 F=_
  rw [nativeL2HalfAllScaleJet_zero_eq_original,nativeLowL2AllScaleJet_zero]

theorem nativeFullL2_value_trace (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeCollarValueTraceCLM (nativeFullL2AllScaleJetCLM P hp v hv hb 0 F)=
      nativeAngularTraceCLM (nativeLowL2AngularCLM v hv hb F 0) := by
  rw [nativeFullL2AllScaleJet_zero,map_add,nativeL2HalfJet_zero_value_trace,zero_add,nativeLowL2Jet_value_trace]

theorem nativeFullL2_normal_trace (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeCollarNormalTraceCLM (nativeFullL2AllScaleJetCLM P hp v hv hb 0 F)=
      nativeL2HalfNormalTraceCLM P hp F+nativeAngularTraceCLM (nativeLowL2NormalAngularCLM v hv hb F) := by
  rw [nativeFullL2AllScaleJet_zero,map_add,nativeLowL2Jet_normal_trace]
  rfl

#print axioms nativeLowL2AllScaleJet_zero
#print axioms nativeFullL2AllScaleJet_zero
#print axioms nativeFullL2_value_trace
#print axioms nativeFullL2_normal_trace
end Yamabe3.Analysis.SpherePolar
