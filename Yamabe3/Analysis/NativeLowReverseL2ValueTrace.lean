import Yamabe3.Analysis.NativeLowReverseL2SameField
import Yamabe3.Analysis.NativeL2HalfValueTrace

/-! The genuine collar value trace of the low solution is its actual
finite low entrance. The proof uses smooth restrictions and density,
not restriction of a volume-a.e. equality to the sphere. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0≤v t ∧ v t≤1)

theorem nativeLowReverseL2Jet_agrees_C2 (F : continuousL2Source AngularSpectralSpace) :
    nativeLowReverseL2JetCLM v hv hb (continuousL2SourceInclusion _ F)=
      nativeC2CollarJetInclusion (nativeLowReverseL2ContinuousFieldLinear v hv hb F) := by
  apply Subtype.ext
  exact nativeLowReverseL2RawJet_agrees_continuous v hv hb F

theorem nativeLowReverseL2Jet_value_trace (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeCollarValueTraceCLM (nativeLowReverseL2JetCLM v hv hb F)=
      nativeAngularTraceCLM (nativeLowL2AngularCLM v hv hb F 0) := by
  have hc := isClosed_eq
    (nativeCollarValueTraceCLM.continuous.comp (nativeLowReverseL2JetCLM v hv hb).continuous)
    (nativeAngularTraceCLM.continuous.comp ((BoundedContinuousFunction.evalCLM ℝ 0).continuous.comp
      (nativeLowL2AngularCLM v hv hb).continuous))
  refine (continuousL2SourceInclusion_dense AngularSpectralSpace).induction_on F hc ?_
  intro H
  rw [nativeLowReverseL2Jet_agrees_C2,(nativeCollarTraceCLM_agrees_C2 _).1]
  apply Lp.ext
  have he := nativeLowReverseL2Joint_ae v hv hb (continuousL2SourceInclusion _ H) 0
  simp only [nativeReverseConjugatedCurve,mul_zero,Real.exp_zero,one_smul,neg_zero] at he
  filter_upwards [nativeC2ValueTraceLinear_ae (nativeLowReverseL2ContinuousFieldLinear v hv hb H),he,
    nativeAngularTraceCLM_ae (nativeLowL2AngularCLM v hv hb (continuousL2SourceInclusion _ H) 0)] with θ ht he hm
  rw [ht,hm]
  change nativeLowReverseL2PhysicalField v hv hb (continuousL2SourceInclusion _ H) (θ:E)=_
  rw [nativeLowReverseL2Physical_eq_lift,native_cylinderLift_sphere]
  exact he

#print axioms nativeLowReverseL2Jet_agrees_C2
#print axioms nativeLowReverseL2Jet_value_trace
end Yamabe3.Analysis.SpherePolar
