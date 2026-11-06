import Yamabe3.Analysis.NativeSupportedScaleZero
import Yamabe3.Analysis.NativeExteriorAllScaleField
import Yamabe3.Analysis.NativeScaledJetRepresentation

/-! The actual support-aware Cauchy solution is one full exterior field:
particular high and low components, computed finite Cauchy correction,
actual entrance subtraction and one prescribed high boundary element.
Every scale is identified with the same joint representative. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

def nativeSupportedParticularJet (τ b s : ℝ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) : nativeCollarJetClosure :=
  nativeBubbleParticularAllScaleJetCLM τ s F+
    nativeLowReverseAllScaleJetCLM (nativeBubbleReverseProfile τ)
      (nativeBubbleReverseProfile_continuous τ) (nativeBubbleReverseProfile_bounds τ) s
        (nativeSupportedReverseSourcePrepareCLM b F)

def nativeSupportedLowCauchyCoefficients (b : ℝ) {τ : ℝ} (ht : 0<τ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2) (i : AngularIndex) (t : ℝ) : ℝ :=
  let dn := nativeBubbleLowCorrectionDataCLM τ (nativeSupportedReverseSourcePrepareCLM b F,(d,n))
  nativeLowCauchyQ ht (nativeLowCauchyCoordinateCLM dn) i (τ+t)

theorem nativeSupportedLowCauchyCoefficients_C2 (b : ℝ) {τ : ℝ} (ht : 0<τ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2) (i : AngularIndex)
    (hi : i∈nativeLowIndexFinset) : ContDiff ℝ 2 (nativeSupportedLowCauchyCoefficients b ht F d n i) :=
  (nativeLowCauchyQ_C2 ht _ i hi).comp (contDiff_const.add contDiff_id)

def nativeSupportedLowCauchyAllScaleJet (b : ℝ) {τ : ℝ} (ht : 0<τ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2) (s : ℝ) : nativeCollarJetClosure :=
  nativeFiniteAllScaleJet nativeLowIndexFinset (nativeSupportedLowCauchyCoefficients b ht F d n)
    (nativeSupportedLowCauchyCoefficients_C2 b ht F d n) s

def nativeSupportedOuterAllScaleJet (b : ℝ) {τ : ℝ} (ht : 0<τ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2)
    (σ : AngularH1) (hσ : NativeAngularSpectralRegular (3/2) (angularEmbedding σ)) (s : ℝ) : nativeCollarJetClosure :=
  nativeSupportedParticularJet τ b s F+nativeSupportedLowCauchyAllScaleJet b ht F d n s-
    nativeExteriorShiftedJet (fullBubbleHighPotential (-τ)) s
      (nativeL2EntranceH1 (fullBubbleHighPotential τ).κ_nonneg (fullBubbleHighPotential τ).κ_lt_one
        (fullBubblePhasePotential τ) (fullBubbleHighPotential τ).kernel_bound (fullBubblePhasePotential_plus_kernel τ) F)
      (nativeL2EntranceH1_spec (fullBubbleHighPotential τ).κ_nonneg (fullBubbleHighPotential τ).κ_lt_one
        (fullBubblePhasePotential τ) (fullBubbleHighPotential τ).kernel_bound (fullBubblePhasePotential_plus_kernel τ) F).2.1+
    nativeExteriorShiftedJet (fullBubbleHighPotential (-τ)) s σ hσ

theorem nativeSupportedOuterAllScaleJet_zero_eq (b : ℝ) {τ : ℝ} (ht : 0<τ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2)
    (σ : AngularH1) (hσ : NativeAngularSpectralRegular (3/2) (angularEmbedding σ)) :
    nativeSupportedOuterAllScaleJet b ht F d n σ hσ 0=
      nativeSupportedBubbleExteriorInhomogeneousJetCLM b ht (F,(d,n))+
        nativePoissonExteriorCollarJet (fullBubbleHighPotential (-τ)) σ hσ := by
  unfold nativeSupportedOuterAllScaleJet nativeSupportedParticularJet nativeSupportedLowCauchyAllScaleJet
  rw [nativeBubbleParticularAllScaleJet_zero_eq,nativeLowReverseAllScaleJet_zero_eq,
    nativeFiniteAllScaleJet_zero_eq,nativeExteriorShiftedJet_zero_eq_original,nativeExteriorShiftedJet_zero_eq_original]
  change _=nativeBubbleLowInhomogeneousJetCLM ht (nativeSupportedReverseSourcePrepareCLM b F,(d,n))+
    nativeExteriorL2HighJetCLM (fullBubbleHighPotential τ) (fullBubbleHighPotential (-τ))
      (fullBubblePhasePotential_plus_kernel τ) F+_
  rw [nativeBubbleLowInhomogeneousJetCLM_eq,nativeExteriorL2HighJetCLM_eq,nativeLowCauchyCollarCLM_eq]
  change nativeL2ParticularJetCLM (fullBubbleHighPotential τ) (fullBubblePhasePotential_plus_kernel τ) F+
    nativeBubbleLowReverseJetCLM τ (nativeSupportedReverseSourcePrepareCLM b F)+
    nativeBubbleLowCollarJet τ
      (nativeLowCauchyQ ht (nativeLowCauchyCoordinateCLM
        (nativeBubbleLowCorrectionDataCLM τ (nativeSupportedReverseSourcePrepareCLM b F,(d,n)))))
      (nativeLowCauchyQ_C2 ht _)-_+_= _
  have hdn : nativeBubbleLowCorrectionDataCLM τ (nativeSupportedReverseSourcePrepareCLM b F,(d,n))=
      (d-nativeBubbleLowEntranceCLM τ (nativeSupportedReverseSourcePrepareCLM b F),
        nativeBubbleLowNormalCLM τ (nativeSupportedReverseSourcePrepareCLM b F)-n-(1/2:ℝ) •
          (d-nativeBubbleLowEntranceCLM τ (nativeSupportedReverseSourcePrepareCLM b F))) := rfl
  rw [hdn]
  have rearrange (A L C H Z : nativeCollarJetClosure) :
      (A+L)+C-H+Z=(L+C)+(A-H)+Z := by
    abel
  exact rearrange _ _ _ _ _

#print axioms nativeSupportedLowCauchyCoefficients_C2
#print axioms nativeSupportedOuterAllScaleJet_zero_eq
end Yamabe3.Analysis.SpherePolar
