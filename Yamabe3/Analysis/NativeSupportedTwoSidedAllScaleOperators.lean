import Yamabe3.Analysis.NativeExteriorShiftedFamilyOperators
import Yamabe3.Analysis.NativeLowCauchyAllScaleOperators
import Yamabe3.Analysis.NativeSupportedOuterPartBounds
import Yamabe3.Analysis.NativeSupportedTwoSidedMatching

/-! Every exterior shell uses ONE bounded linear field from the SAME
source pair and coupled sigma. All finite low compensation terms and
the actual entrance subtraction are retained in the all-scale producer. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic

private def supportedParticularCLM (τ b s:ℝ) :
    Lp AngularSpectralSpace 2 (volume:Measure ℝ) →L[ℝ] nativeCollarJetClosure :=
  nativeBubbleParticularAllScaleJetCLM τ s+
    (nativeLowReverseAllScaleJetCLM (nativeBubbleReverseProfile τ)
      (nativeBubbleReverseProfile_continuous τ) (nativeBubbleReverseProfile_bounds τ) s).comp
        (nativeSupportedReverseSourcePrepareCLM b)

theorem exists_nativeSupportedTwoSided_all_scale_CLM
    (P:NativeHighPotential)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
    (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0≤v t ∧ v t≤1) (b:ℝ) {τ:ℝ} (ht:0<τ) :
    ∃C:ℝ,0≤C ∧ ∀s:ℝ,s≤0 →
      ∃J:NativeTwoSidedSource →L[ℝ] nativeCollarJetClosure,‖J‖≤C ∧
        ∀X:NativeTwoSidedSource,
          J X=nativeSupportedOuterAllScaleJet b ht X.2
            (nativeLowL2AngularCLM v hv hb X.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.1)
            (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X)
            (nativeTwoSidedSourceSigma_regular P hp v hv hb τ X) s := by
  let Q:=fullBubbleHighPotential τ
  let B:=fullBubbleHighPotential (-τ)
  let T0:=nativeL2EntranceH1CLM Q.κ_nonneg Q.κ_lt_one Q.potential Q.kernel_bound
    (fullBubblePhasePotential_plus_kernel τ)
  have hT0 F:NativeAngularSpectralRegular (3/2) (angularEmbedding (T0 F)) :=
    (nativeL2EntranceH1_spec Q.κ_nonneg Q.κ_lt_one Q.potential Q.kernel_bound
      (fullBubblePhasePotential_plus_kernel τ) F).2.1
  have hE0:∃D:ℝ,0≤D ∧ ∀F,(∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding (T0 F)) i)≤D*‖F‖^2 :=
    ⟨(50/9)*(1+‖Q.potential‖*((1-Q.κ)⁻¹*(4/9)))^2,by positivity,
      fun F=>(nativeL2EntranceH1_spec Q.κ_nonneg Q.κ_lt_one Q.potential Q.kernel_bound
        (fullBubblePhasePotential_plus_kernel τ) F).2.2.1⟩
  let Tσ:=nativeTwoSidedSourceSigmaCLM P hp v hv hb τ
  have hTσ X:NativeAngularSpectralRegular (3/2) (angularEmbedding (Tσ X)) :=
    nativeTwoSidedSourceSigma_regular P hp v hv hb τ X
  have hEσ:∃D:ℝ,0≤D ∧ ∀X,(∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding (Tσ X)) i)≤D*‖X‖^2 := by
    obtain ⟨D,hD,hd⟩:=exists_nativeTwoSidedSourceSigma_energy P hp v hv hb τ
    refine ⟨D,hD,fun X=>?_⟩
    exact (le_add_of_nonneg_left (sq_nonneg ‖Tσ X‖)).trans (hd X)
  obtain ⟨C0,hC0,h0⟩:=exists_nativeExteriorShiftedFamilyJetCLM B T0 hT0 hE0
  obtain ⟨Cσ,hCσ,hσ⟩:=exists_nativeExteriorShiftedFamilyJetCLM B Tσ hTσ hEσ
  obtain ⟨CQ,hCQ,hQ⟩:=exists_nativeLowCauchyAllScaleJetCLM ht
  obtain ⟨CP,hCP,hP⟩:=exists_nativeSupportedParticular_halfEnd_bound τ b
  let D:=nativeLowCauchyCoordinateCLM.comp ((nativeBubbleLowCorrectionDataCLM τ).comp
    ((nativeSupportedLowPhysicalDataCLM b).comp (nativeTwoSidedExteriorDataCLM P hp v hv hb)))
  let C:=CP+CQ*‖D‖+C0+Cσ
  have hC:0≤C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro s hs
  obtain ⟨J0,hJ0,hJ0v⟩:=h0 s hs
  obtain ⟨Jσ,hJσ,hJσv⟩:=hσ s hs
  obtain ⟨JQ,hJQ,hJQv⟩:=hQ s hs
  let fst:=ContinuousLinearMap.snd ℝ
    (Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (Lp AngularSpectralSpace 2 (volume:Measure ℝ))
  let JP:=(supportedParticularCLM τ b s).comp fst
  let J:=JP+JQ.comp D-J0.comp fst+Jσ
  have hJP X:‖JP X‖≤CP*‖X‖ :=
    (hP X.2 s hs).trans (mul_le_mul_of_nonneg_left (norm_snd_le X) hCP)
  have hQX X:‖JQ (D X)‖≤(CQ*‖D‖)*‖X‖ :=
    ((JQ.le_opNorm _).trans (mul_le_mul_of_nonneg_right hJQ (norm_nonneg _))).trans
      ((mul_le_mul_of_nonneg_left (D.le_opNorm _) hCQ).trans_eq (by ring))
  have h0X X:‖J0 (fst X)‖≤C0*‖X‖ :=
    (J0.le_opNorm _).trans (mul_le_mul hJ0 (norm_snd_le X) (norm_nonneg _) hC0)
  have hσX X:‖Jσ X‖≤Cσ*‖X‖ :=
    (Jσ.le_opNorm _).trans (mul_le_mul_of_nonneg_right hJσ (norm_nonneg _))
  have hbound X:‖J X‖≤C*‖X‖ := by
    change ‖(JP X+JQ (D X)-J0 (fst X))+Jσ X‖≤_
    apply (norm_add_le _ _).trans
    apply (add_le_add (norm_sub_le _ _) le_rfl).trans
    apply (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl).trans
    exact (add_le_add (add_le_add (add_le_add (hJP X) (hQX X)) (h0X X)) (hσX X)).trans_eq (by dsimp only [C];ring)
  refine ⟨J,J.opNorm_le_bound hC hbound,?_⟩
  intro X
  change supportedParticularCLM τ b s X.2+JQ (D X)-J0 X.2+Jσ X=_
  rw [hJQv,hJ0v,hJσv]
  rfl

#print axioms exists_nativeSupportedTwoSided_all_scale_CLM
end Yamabe3.Analysis.SpherePolar
