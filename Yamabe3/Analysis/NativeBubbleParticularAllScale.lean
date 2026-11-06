import Yamabe3.Analysis.NativeBubbleParticularFarEnd
import Yamabe3.Analysis.NativeL2ShiftedCollar
import Yamabe3.Analysis.NativeL2CollarJetClosure
import Yamabe3.Analysis.NativeAllScaleLocalH2

/-! The literal bubble particular field on all physical scales. The
actual translated phase is proved, and all jets belong to one field.
This is the high inhomogeneous part before boundary correction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

theorem fullBubblePhasePotential_translate (τ s : ℝ) :
    fullBubblePhasePotential (τ+s)=boundedTimeTranslate ℝ s (fullBubblePhasePotential τ) := by
  ext t
  change (15/4:ℝ)*fullBubbleDensity (t+(τ+s))=(15/4)*fullBubbleDensity (t+s+τ)
  rw [show t+(τ+s)=t+s+τ by ring]

def nativeBubbleParticularAllScaleJetCLM (τ s : ℝ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] nativeCollarJetClosure :=
  (nativeL2ParticularJetCLM (fullBubbleHighPotential (τ+s)) (fullBubblePhasePotential_plus_kernel (τ+s))).comp
    (l2TimeTranslateCLM AngularSpectralSpace s)

def nativeBubbleParticularAllScaleRawJetCLM (τ s : ℝ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] NativeCollarJet :=
  nativeCollarJetClosure.subtypeL.comp (nativeBubbleParticularAllScaleJetCLM τ s)

theorem nativeBubbleParticularAllScale_equation (τ s : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s (fullBubblePhasePotential τ))
      (nativeBubbleParticularAllScaleRawJetCLM τ s F)=
        -nativeL2HighPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F) := by
  rw [←fullBubblePhasePotential_translate]
  let P := fullBubbleHighPotential (τ+s)
  let hp := fullBubblePhasePotential_plus_kernel (τ+s)
  let Fs := l2TimeTranslateCLM AngularSpectralSpace s F
  change -((∑j : Fin 3,nativeL2ParticularSecondCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp j j Fs)+
    nativeCollarPotentialMulCLM P.potential (nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp Fs))=_
  rw [nativeL2Particular_physical_equation]

theorem nativeBubbleParticularAllScale_same_field (τ : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    ∃w : ℝ×S→ℝ,Measurable w ∧
      (∀t,(fun θ => w (t,θ))=ᵐ[angularVolume]
        (nativeConjugatedCurve (nativeL2ParticularAngularCLM (fullBubblePhasePotential τ) F) t : S→ℝ)) ∧
      ∀s : ℝ,((nativeBubbleParticularAllScaleRawJetCLM τ s F).1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) := by
  let P := fullBubbleHighPotential τ
  obtain ⟨w,hw,hae,hj⟩ := nativeL2ShiftedCollar_same_physical_function P.κ_nonneg P.κ_lt_one
    P.potential P.kernel_bound (fullBubblePhasePotential_plus_kernel τ) F
  refine ⟨w,hw,hae,fun s => ?_⟩
  have h := (hj s).1
  change (nativeL2ParticularValueCLM (fullBubbleHighPotential (τ+s)).κ_nonneg
    (fullBubbleHighPotential (τ+s)).κ_lt_one (fullBubblePhasePotential (τ+s))
    (fullBubbleHighPotential (τ+s)).kernel_bound (fullBubblePhasePotential_plus_kernel (τ+s))
    (l2TimeTranslateCLM AngularSpectralSpace s F) : E→ℝ)=ᵐ[_] _
  simpa only [P,fullBubbleHighPotential,←fullBubblePhasePotential_translate] using h

theorem nativeBubbleParticularAllScale_memH2 (τ s : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    MemWkp 2 2 (nativeBubbleParticularAllScaleRawJetCLM τ s F).1 nativePoissonEntranceCollar :=
  nativeCollarJetClosure_memH2 (nativeBubbleParticularAllScaleJetCLM τ s F)

theorem exists_nativeBubbleParticular_same_field_localH2 (τ : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    ∃w : ℝ×S→ℝ,Measurable w ∧ MemWkpLocally 2 (cylinderLift w) ({0}ᶜ : Set E) ∧
      (∀t,(fun θ => w (t,θ))=ᵐ[angularVolume]
        (nativeConjugatedCurve (nativeL2ParticularAngularCLM (fullBubblePhasePotential τ) F) t : S→ℝ)) ∧
      ∀s : ℝ,((nativeBubbleParticularAllScaleRawJetCLM τ s F).1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) := by
  obtain ⟨w,hw,hae,hj⟩ := nativeBubbleParticularAllScale_same_field τ F
  exact ⟨w,hw,native_all_scale_H2_local (fun s =>
    (MemWkp_congr_ae (by norm_num) (nativePolarTimeWindow_open (1/2)) (hj s)).mp
      (nativeBubbleParticularAllScale_memH2 τ s F)),hae,hj⟩

#print axioms fullBubblePhasePotential_translate
#print axioms nativeBubbleParticularAllScale_equation
#print axioms nativeBubbleParticularAllScale_same_field
#print axioms nativeBubbleParticularAllScale_memH2
#print axioms exists_nativeBubbleParticular_same_field_localH2
end Yamabe3.Analysis.SpherePolar
