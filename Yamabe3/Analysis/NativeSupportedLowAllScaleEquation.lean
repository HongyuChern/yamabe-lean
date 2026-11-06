import Yamabe3.Analysis.NativeLowReverseAllScale
import Yamabe3.Analysis.NativeSupportedReverseTranslation
import Yamabe3.Analysis.NativeOrbitCollarJacobian

/-! One original source drives the actual low equation at every physical
scale. The exact inverse-fourth weight, time reflection and scale factor
are all cancelled by proved L2 identities. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
variable (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)

theorem nativeLowReversePotential_translate (s : ℝ) :
    nativeLowReversePotential (fun t => v (t+ -s)) (hv.comp (continuous_id.add continuous_const))
      (fun t => hb (t+ -s))=boundedTimeTranslate ℝ s (nativeLowReversePotential v hv hb) := by
  ext t
  change (15/4:ℝ)*v ((-t+0)+ -s)^4=(15/4)*v (-(t+s)+0)^4
  congr 3
  ring

theorem nativeFlatCollarJet_low_reverse (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeFlatCollarJetCLM (nativeLowReversePotential v hv hb) (nativeLowReverseL2RawJetCLM v hv hb F)=
      -nativeLowReverseL2SourceCLM F := by
  change -((∑j : Fin 3,(nativeLowReverseL2RawJetCLM v hv hb F).2.2 j j)+
    nativeCollarPotentialMulCLM (nativeLowReversePotential v hv hb) (nativeLowReverseL2RawJetCLM v hv hb F).1)=_
  rw [nativeLowReverseL2_physical_equation]

def nativeSupportedLowAllScaleRawJetCLM (b s : ℝ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] NativeCollarJet :=
  (nativeLowReverseAllScaleRawJetCLM v hv hb s).comp (nativeSupportedReverseSourcePrepareCLM b)

theorem nativeSupportedLowAllScale_equation (b s : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (hF : ∀ᵐt : ℝ ∂volume,t<b → F t=0) :
    nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s (nativeLowReversePotential v hv hb))
      (nativeSupportedLowAllScaleRawJetCLM v hv hb b s F)=
        -nativeL2LowPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F) := by
  change nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s (nativeLowReversePotential v hv hb))
    (Real.exp (4*s) • nativeLowReverseL2RawJetCLM (fun t => v (t+ -s))
      (hv.comp (continuous_id.add continuous_const)) (fun t => hb (t+ -s))
        (l2TimeTranslateCLM AngularSpectralSpace (-s) (nativeSupportedReverseSourcePrepareCLM b F)))=_
  rw [map_smul,←nativeLowReversePotential_translate,nativeFlatCollarJet_low_reverse,smul_neg,
    nativeSupportedReverseSource_all_scale_reconstruction b s F hF]

theorem nativeSupportedLowAllScale_same_field (b s : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    ((nativeSupportedLowAllScaleRawJetCLM v hv hb b s F).1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*s/2)*nativeLowReverseL2PhysicalField v hv hb
        (nativeSupportedReverseSourcePrepareCLM b F) (Real.exp (-s) • x)) :=
  nativeLowReverseAllScale_same_field v hv hb s _

theorem nativeSupportedLowPhysical_localH2 (b : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    MemWkpLocally 2 (nativeLowReverseL2PhysicalField v hv hb (nativeSupportedReverseSourcePrepareCLM b F)) ({0}ᶜ : Set E) :=
  nativeLowReversePhysical_localH2 v hv hb _

omit v hv hb in
theorem exists_uniform_nativeSupportedLowAllScale_bound :
    ∃B : ℝ,0<B ∧ ∀(v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1) (b s : ℝ),
      ‖nativeSupportedLowAllScaleRawJetCLM v hv hb b s‖≤B*Real.exp (4*(s-b)) := by
  obtain ⟨B,hB,hd⟩ := exists_uniform_nativeLowReverseAllScale_bound
  refine ⟨B,hB,fun v hv hb b s => ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun F => ?_)⟩
  have h := (nativeLowReverseAllScaleRawJetCLM v hv hb s).le_of_opNorm_le (hd v hv hb s)
    (nativeSupportedReverseSourcePrepareCLM b F)
  have he := nativeSupportedReverseSourcePrepare_bound b F
  apply (h.trans (mul_le_mul_of_nonneg_left he (by positivity : 0≤B*Real.exp (4*s)))).trans_eq
  calc
    _ = B*(Real.exp (4*s)*Real.exp (-4*b))*‖F‖ := by ring
    _ = _ := by rw [←Real.exp_add];congr 2;congr 1;ring

#print axioms nativeLowReversePotential_translate
#print axioms nativeFlatCollarJet_low_reverse
#print axioms nativeSupportedLowAllScale_equation
#print axioms nativeSupportedLowAllScale_same_field
#print axioms nativeSupportedLowPhysical_localH2
#print axioms exists_uniform_nativeSupportedLowAllScale_bound
end Yamabe3.Analysis.SpherePolar
