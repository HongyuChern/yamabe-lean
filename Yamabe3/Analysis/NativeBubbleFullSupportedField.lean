import Yamabe3.Analysis.NativeBubbleParticularAllScale
import Yamabe3.Analysis.NativeSupportedLowAllScaleEquation
import Yamabe3.Analysis.NativeBubbleLowReverseSolver

/-! A genuine full-mode bubble particular field for one supported L2
source, on every scale. High and low have the same physical source and
potential. Boundary correction is not included in this module. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

def nativeBubbleFullSupportedAllScaleRawJetCLM (τ b s : ℝ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] NativeCollarJet :=
  nativeBubbleParticularAllScaleRawJetCLM τ s+
    nativeSupportedLowAllScaleRawJetCLM (nativeBubbleReverseProfile τ)
      (nativeBubbleReverseProfile_continuous τ) (nativeBubbleReverseProfile_bounds τ) b s

def nativeBubbleFullSupportedCurve (τ b : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (t : ℝ) : AngularL2 :=
  nativeConjugatedCurve (nativeL2ParticularAngularCLM (fullBubblePhasePotential τ) F) t+
    nativeReverseConjugatedCurve (nativeLowL2AngularCLM (nativeBubbleReverseProfile τ)
      (nativeBubbleReverseProfile_continuous τ) (nativeBubbleReverseProfile_bounds τ)
        (nativeSupportedReverseSourcePrepareCLM b F)) t

theorem nativeBubbleFullSupportedAllScale_equation (τ b s : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (hF : ∀ᵐt : ℝ ∂volume,t<b → F t=0) :
    nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s (fullBubblePhasePotential τ))
      (nativeBubbleFullSupportedAllScaleRawJetCLM τ b s F)=
        -nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F) := by
  have hl := nativeSupportedLowAllScale_equation (nativeBubbleReverseProfile τ)
    (nativeBubbleReverseProfile_continuous τ) (nativeBubbleReverseProfile_bounds τ) b s F hF
  rw [nativeBubbleReversePotential_eq,nativeBubbleExteriorPotential_eq_phase] at hl
  change nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s (fullBubblePhasePotential τ))
    (nativeBubbleParticularAllScaleRawJetCLM τ s F+
      nativeSupportedLowAllScaleRawJetCLM (nativeBubbleReverseProfile τ)
        (nativeBubbleReverseProfile_continuous τ) (nativeBubbleReverseProfile_bounds τ) b s F)=_
  rw [map_add,nativeBubbleParticularAllScale_equation,hl,←neg_add,nativeL2High_add_low_source]

theorem nativeBubbleFullSupportedAllScale_memH2 (τ b s : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    MemWkp 2 2 (nativeBubbleFullSupportedAllScaleRawJetCLM τ b s F).1 nativePoissonEntranceCollar := by
  have hH := (nativeBubbleParticularAllScaleJetCLM τ s F).property
  have hL := (nativeLowReverseAllScaleJetCLM (nativeBubbleReverseProfile τ)
    (nativeBubbleReverseProfile_continuous τ) (nativeBubbleReverseProfile_bounds τ) s
      (nativeSupportedReverseSourcePrepareCLM b F)).property
  exact nativeCollarJetClosure_memH2 ⟨_,nativeCollarJetClosure.add_mem hH hL⟩

theorem nativeBubbleFullSupported_same_field (τ b : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    ∃w : ℝ×S→ℝ,Measurable w ∧
      (∀t,(fun θ => w (t,θ))=ᵐ[angularVolume](nativeBubbleFullSupportedCurve τ b F t : S→ℝ)) ∧
      ∀s : ℝ,((nativeBubbleFullSupportedAllScaleRawJetCLM τ b s F).1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) := by
  obtain ⟨w,hw,hae,hj⟩ := nativeBubbleParticularAllScale_same_field τ F
  let v := nativeBubbleReverseProfile τ
  let hv := nativeBubbleReverseProfile_continuous τ
  let hb := nativeBubbleReverseProfile_bounds τ
  let G := nativeSupportedReverseSourcePrepareCLM b F
  let q := nativeLowReverseL2Joint v hv hb G
  have hq := (nativeLowReverseL2Joint_continuous v hv hb G).measurable
  refine ⟨fun z => w z+q z,hw.add hq,fun t => ?_,fun s => ?_⟩
  · have hs := (ae_restrict_iff' MeasurableSet.univ).mp (Lp.coeFn_add
      (nativeConjugatedCurve (nativeL2ParticularAngularCLM (fullBubblePhasePotential τ) F) t)
      (nativeReverseConjugatedCurve (nativeLowL2AngularCLM v hv hb G) t))
    filter_upwards [hae t,nativeLowReverseL2Joint_ae v hv hb G t,hs] with θ ht hqt hsθ
    change q (t,θ)=_ at hqt
    rw [ht,hqt]
    exact (hsθ (mem_univ θ)).symm
  · have hl := nativeSupportedLowAllScale_same_field v hv hb b s F
    have ha := Lp.coeFn_add (nativeBubbleParticularAllScaleRawJetCLM τ s F).1
      (nativeSupportedLowAllScaleRawJetCLM v hv hb b s F).1
    filter_upwards [ha,hj s,hl] with x ha hh hl
    change ((nativeBubbleParticularAllScaleRawJetCLM τ s F).1+
      (nativeSupportedLowAllScaleRawJetCLM v hv hb b s F).1 : NativeCollarL2) x=_
    rw [ha]
    change (nativeBubbleParticularAllScaleRawJetCLM τ s F).1 x+
      (nativeSupportedLowAllScaleRawJetCLM v hv hb b s F).1 x=_
    rw [hh,hl,nativeLowReverseL2Physical_eq_lift,native_cylinderLift_add]
    exact (mul_add _ _ _).symm

theorem exists_nativeBubbleFullSupported_same_source_localH2 (τ b : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (hF : ∀ᵐt : ℝ ∂volume,t<b → F t=0) :
    ∃w : ℝ×S→ℝ,Measurable w ∧ MemWkpLocally 2 (cylinderLift w) ({0}ᶜ : Set E) ∧
      (∀t,(fun θ => w (t,θ))=ᵐ[angularVolume](nativeBubbleFullSupportedCurve τ b F t : S→ℝ)) ∧
      ∀s : ℝ,((nativeBubbleFullSupportedAllScaleRawJetCLM τ b s F).1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) ∧
      nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s (fullBubblePhasePotential τ))
        (nativeBubbleFullSupportedAllScaleRawJetCLM τ b s F)=
          -nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F) := by
  obtain ⟨w,hw,hae,hj⟩ := nativeBubbleFullSupported_same_field τ b F
  refine ⟨w,hw,native_all_scale_H2_local (fun s => ?_),hae,fun s => ⟨hj s,nativeBubbleFullSupportedAllScale_equation τ b s F hF⟩⟩
  exact (MemWkp_congr_ae (by norm_num) (nativePolarTimeWindow_open (1/2)) (hj s)).mp
    (nativeBubbleFullSupportedAllScale_memH2 τ b s F)

#print axioms nativeBubbleFullSupportedAllScale_equation
#print axioms nativeBubbleFullSupportedAllScale_memH2
#print axioms nativeBubbleFullSupported_same_field
#print axioms exists_nativeBubbleFullSupported_same_source_localH2
end Yamabe3.Analysis.SpherePolar
