import Yamabe3.Analysis.NativeSupportedOuterAllScaleEquation
import Yamabe3.Analysis.NativeSupportedTwoSidedMatching

/-! The same two-sided source and coupled boundary element produce one
actual exterior field on every scale. Its scale-zero jet is precisely the
already matched physical Cauchy jet, not a separately selected solution. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
variable (P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)
  (b : ℝ) {τ : ℝ} (ht : 0<τ)

def nativeSupportedTwoSidedExteriorAllScaleJet (X : NativeTwoSidedSource) (s : ℝ) : nativeCollarJetClosure :=
  nativeSupportedOuterAllScaleJet b ht X.2 (nativeLowL2AngularCLM v hv hb X.1 0)
    (nativeFullL2NormalAngularCLM P hp v hv hb X.1)
    (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X) (nativeTwoSidedSourceSigma_regular P hp v hv hb τ X) s

theorem nativeSupportedTwoSidedExteriorAllScale_zero_eq (X : NativeTwoSidedSource) :
    nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht X 0=
      nativeSupportedTwoSidedExteriorJetCLM P hp v hv hb b ht X := by
  unfold nativeSupportedTwoSidedExteriorAllScaleJet
  rw [nativeSupportedOuterAllScaleJet_zero_eq]
  exact (nativeSupportedTwoSidedExteriorJetCLM_eq P hp v hv hb b ht X).symm

theorem nativeSupportedTwoSidedExteriorAllScale_matching (X : NativeTwoSidedSource) :
    nativeCollarValueTraceCLM (nativeTwoSidedInteriorJetCLM P hp v hv hb τ X)=
      nativeCollarValueTraceCLM (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht X 0) ∧
    nativeCollarNormalTraceCLM (nativeTwoSidedInteriorJetCLM P hp v hv hb τ X)=
      nativeCollarNormalTraceCLM (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht X 0) ∧
    NativeCollarWeakGluing (nativeTwoSidedInteriorJetCLM P hp v hv hb τ X)
      (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht X 0) := by
  rw [nativeSupportedTwoSidedExteriorAllScale_zero_eq]
  have h := nativeSupportedTwoSidedSource_actual_matching P hp v hv hb b ht X
  exact ⟨h.1,h.2,nativeSupportedTwoSidedSource_actual_weak_gluing P hp v hv hb b ht X⟩

theorem exists_nativeSupportedTwoSidedExterior_same_field_equation (X : NativeTwoSidedSource)
    (hX : ∀ᵐt : ℝ ∂volume,t<b → X.2 t=0) :
    ∃w : ℝ×S→ℝ,Measurable w ∧ MemWkpLocally 2 (cylinderLift w) ({0}ᶜ : Set E) ∧
      (∀s : ℝ,NativeScaledJetRep (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht X s) s w ∧
        MemWkp 2 2 (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht X s).val.1 nativePoissonEntranceCollar ∧
        (nativeNegativeScaledRestrictionCLM s
          (nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s (fullBubblePhasePotential τ))
            (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht X s).val) : E→ℝ)
          =ᵐ[volume.restrict (nativeNegativeScaledCollar s)]
          (fun x => -(nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s X.2) : E→ℝ) x+
            nativeSupportedLowCompensationScaled b ht X.2 (nativeLowL2AngularCLM v hv hb X.1 0)
              (nativeFullL2NormalAngularCLM P hp v hv hb X.1) s x)) ∧
      NativeCollarWeakGluing (nativeTwoSidedInteriorJetCLM P hp v hv hb τ X)
        (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht X 0) := by
  obtain ⟨w,hw,hlocal,hj⟩ := exists_nativeSupportedOuter_same_field_all_scale b ht X.2
    (nativeLowL2AngularCLM v hv hb X.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.1)
    (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X) (nativeTwoSidedSourceSigma_regular P hp v hv hb τ X)
  refine ⟨w,hw,hlocal,fun s => ⟨(hj s).1,(hj s).2,?_⟩,
    (nativeSupportedTwoSidedExteriorAllScale_matching P hp v hv hb b ht X).2.2⟩
  exact nativeSupportedOuterAllScale_source b ht X.2 (nativeLowL2AngularCLM v hv hb X.1 0)
    (nativeFullL2NormalAngularCLM P hp v hv hb X.1)
    (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X) (nativeTwoSidedSourceSigma_regular P hp v hv hb τ X) hX s

#print axioms nativeSupportedTwoSidedExteriorAllScale_zero_eq
#print axioms nativeSupportedTwoSidedExteriorAllScale_matching
#print axioms exists_nativeSupportedTwoSidedExterior_same_field_equation
end Yamabe3.Analysis.SpherePolar
