import Yamabe3.Analysis.NativeTwoSidedSourceCoupling
import Yamabe3.Analysis.NativeFullBoundaryAllScale

/-! One pair of bounded, genuine H2 collar producers for the two actual
sources. Both sides use exactly the same coupled boundary element.
No source/normal data are chosen again when a test or estimate changes. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable (P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)

private theorem exterior_energy (t₀ : ℝ) :
    ∃D : ℝ,0≤D ∧ ∀X : NativeTwoSidedSource,
      (∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X)) i)≤D*‖X‖^2 := by
  obtain ⟨D,hD,hd⟩ := exists_nativeTwoSidedSourceSigma_energy P hp v hv hb t₀
  refine ⟨D,hD,fun X => ?_⟩
  have h := hd X
  unfold nativePoissonBoundaryEnergy at h
  linarith [sq_nonneg ‖nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X‖]

def nativeTwoSidedInteriorPoissonJetCLM (t₀ : ℝ) : NativeTwoSidedSource →L[ℝ] nativeCollarJetClosure :=
  nativeBoundaryPoissonJetCLM P hp (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀)
    (nativeTwoSidedSourceSigma_regular P hp v hv hb t₀)
    (exists_nativeTwoSidedSourceSigma_energy P hp v hv hb t₀) 0

def nativeTwoSidedExteriorPoissonJetCLM (t₀ : ℝ) : NativeTwoSidedSource →L[ℝ] nativeCollarJetClosure :=
  nativeExteriorBoundaryJetCLM (fullBubbleHighPotential (-t₀)) (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀)
    (nativeTwoSidedSourceSigma_regular P hp v hv hb t₀) (exterior_energy P hp v hv hb t₀)

theorem nativeTwoSidedInteriorPoisson_eq (t₀ : ℝ) (X : NativeTwoSidedSource) :
    nativeTwoSidedInteriorPoissonJetCLM P hp v hv hb t₀ X=
      nativePoissonCollarJet P (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X)
        (nativeTwoSidedSourceSigma_regular P hp v hv hb t₀ X) := by
  let b := nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X
  have hspec := nativeTwoSidedSourceSigma_regular P hp v hv hb t₀ X
  obtain ⟨w,hw,hae,_⟩ := nativePoissonReflectedCurve_joint_representative P b
  have hs := nativePoissonAllScaleValue_same_field P hp b hspec hw.measurable hae 0
  have he := nativePoissonCollarValue_eq_lift P b hspec hw.measurable hae
  apply nativeCollarJet_value_injective
  apply Lp.ext
  have hs0 : (nativePoissonAllScaleValue P hp 0 b : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w := by
    simpa only [mul_zero,zero_div,neg_zero,Real.exp_zero,one_mul,one_smul] using hs
  exact hs0.trans he.symm

theorem nativeTwoSidedExteriorPoisson_eq (t₀ : ℝ) (X : NativeTwoSidedSource) :
    nativeTwoSidedExteriorPoissonJetCLM P hp v hv hb t₀ X=
      nativePoissonExteriorCollarJet (fullBubbleHighPotential (-t₀)) (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X)
        (nativeTwoSidedSourceSigma_regular P hp v hv hb t₀ X) := rfl

def nativeTwoSidedInteriorJetCLM (t₀ : ℝ) : NativeTwoSidedSource →L[ℝ] nativeCollarJetClosure :=
  (nativeFullL2AllScaleJetCLM P hp v hv hb 0).comp (ContinuousLinearMap.fst ℝ _ _)+
    nativeTwoSidedInteriorPoissonJetCLM P hp v hv hb t₀

def nativeTwoSidedExteriorDataCLM : NativeTwoSidedSource →L[ℝ] NativeLowInhomogeneousData :=
  let fst := ContinuousLinearMap.fst ℝ (Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (Lp AngularSpectralSpace 2 (volume : Measure ℝ))
  let d := ((BoundedContinuousFunction.evalCLM ℝ 0).comp (nativeLowL2AngularCLM v hv hb)).comp fst
  let n := (nativeFullL2NormalAngularCLM P hp v hv hb).comp fst
  (ContinuousLinearMap.snd ℝ _ _).prod (d.prod n)

def nativeTwoSidedExteriorJetCLM {t₀ : ℝ} (ht : 0<t₀) : NativeTwoSidedSource →L[ℝ] nativeCollarJetClosure :=
  (nativeBubbleExteriorInhomogeneousJetCLM ht).comp (nativeTwoSidedExteriorDataCLM P hp v hv hb)+
    nativeTwoSidedExteriorPoissonJetCLM P hp v hv hb t₀

theorem nativeTwoSidedInteriorJetCLM_eq (t₀ : ℝ) (X : NativeTwoSidedSource) :
    nativeTwoSidedInteriorJetCLM P hp v hv hb t₀ X=nativeFullL2AllScaleJetCLM P hp v hv hb 0 X.1+
      nativePoissonCollarJet P (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X)
        (nativeTwoSidedSourceSigma_regular P hp v hv hb t₀ X) := by
  change _+nativeTwoSidedInteriorPoissonJetCLM P hp v hv hb t₀ X=_
  rw [nativeTwoSidedInteriorPoisson_eq]
  rfl

theorem nativeTwoSidedExteriorJetCLM_eq {t₀ : ℝ} (ht : 0<t₀) (X : NativeTwoSidedSource) :
    nativeTwoSidedExteriorJetCLM P hp v hv hb ht X=
      nativeBubbleExteriorInhomogeneousJetCLM ht
        (X.2,(nativeLowL2AngularCLM v hv hb X.1 0,nativeFullL2NormalAngularCLM P hp v hv hb X.1))+
      nativePoissonExteriorCollarJet (fullBubbleHighPotential (-t₀)) (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X)
        (nativeTwoSidedSourceSigma_regular P hp v hv hb t₀ X) := rfl

#print axioms nativeTwoSidedInteriorPoisson_eq
#print axioms nativeTwoSidedExteriorPoisson_eq
#print axioms nativeTwoSidedInteriorJetCLM_eq
#print axioms nativeTwoSidedExteriorJetCLM_eq
end Yamabe3.Analysis.SpherePolar
