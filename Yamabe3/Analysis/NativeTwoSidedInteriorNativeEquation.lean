import Yamabe3.Analysis.NativeTwoSidedExteriorNativeEquation

/-! Actual inner collar equation for the same two-sided feedback pair.
The potential identity is discharged for the actual orbit in the assembly.
All residuals are cancelled using the physical source right inverse. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic Yamabe3.Analysis.GreenParametrix
variable (P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)

private theorem full_zero_equation
    (hpot : P.potential=delaunayPhasePotentialBCF v hv hb 0)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativePositiveCollarRestrictionCLM
      ((∑j : Fin 3,(nativeFullL2AllScaleRawJetCLM P hp v hv hb 0 F).2.2 j j)+
        nativeCollarPotentialMulCLM P.potential (nativeFullL2AllScaleRawJetCLM P hp v hv hb 0 F).1)=
      nativePositiveCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM F) := by
  have h := nativeFullL2AllScale_equation P hp v hv hb hpot 0 F
  have hV : boundedTimeTranslate ℝ 0 P.potential=P.potential := by
    apply BoundedContinuousFunction.ext
    intro t
    change P.potential (t+0)=P.potential t
    rw [add_zero]
  have hF : l2TimeTranslateCLM AngularSpectralSpace 0 F=F := by
    apply Lp.ext
    simpa only [add_zero] using l2TimeTranslate_ae AngularSpectralSpace 0 F
  rw [hV,hF] at h
  let A := (∑j : Fin 3,(nativeFullL2AllScaleRawJetCLM P hp v hv hb 0 F).2.2 j j)+
    nativeCollarPotentialMulCLM P.potential (nativeFullL2AllScaleRawJetCLM P hp v hv hb 0 F).1
  let B := nativeL2FullPhysicalSourceCLM F
  have ha : (nativePositiveScaledRestrictionCLM 0 A : E→ℝ)=ᵐ[volume.restrict (nativePositiveScaledCollar 0)] (A : E→ℝ) :=
    l2MeasureRestrict_ae (Measure.restrict_mono inter_subset_left le_rfl) A
  have hb' : (nativePositiveScaledRestrictionCLM 0 B : E→ℝ)=ᵐ[volume.restrict (nativePositiveScaledCollar 0)] (B : E→ℝ) :=
    l2MeasureRestrict_ae (Measure.restrict_mono inter_subset_left le_rfl) B
  have he : (A : E→ℝ)=ᵐ[volume.restrict (nativePositiveScaledCollar 0)] (B : E→ℝ) := by
    change nativePositiveScaledRestrictionCLM 0 A=nativePositiveScaledRestrictionCLM 0 B at h
    rw [h] at ha
    exact ha.symm.trans hb'
  simp only [nativePositiveScaledCollar,Real.exp_zero] at he
  apply Lp.ext
  exact (nativePositiveCollarRestrictionCLM_ae A).trans (he.trans (nativePositiveCollarRestrictionCLM_ae B).symm)

theorem nativeTwoSidedInterior_flat_source
    (hpot : P.potential=delaunayPhasePotentialBCF v hv hb 0)
    (t₀ : ℝ) (X : NativeTwoSidedSource) :
    nativePositiveCollarRestrictionCLM (nativeFlatCollarJetCLM P.potential
      (nativeTwoSidedInteriorJetCLM P hp v hv hb t₀ X).val)=
      -nativePositiveCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM X.1) := by
  rw [nativeTwoSidedInteriorJetCLM_eq,Submodule.coe_add,map_add,map_add]
  have hh := full_zero_equation P hp v hv hb hpot X.1
  have hl := nativePoissonCollar_homogeneous P (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X)
    (nativeTwoSidedSourceSigma_regular P hp v hv hb t₀ X)
  simp only [nativeFlatCollarJetCLM,ContinuousLinearMap.neg_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,nativeCollarJetSecondCLM,
    nativeCollarJetValueCLM,map_neg]
  change -nativePositiveCollarRestrictionCLM
    ((∑j : Fin 3,(nativeFullL2AllScaleRawJetCLM P hp v hv hb 0 X.1).2.2 j j)+
      nativeCollarPotentialMulCLM P.potential (nativeFullL2AllScaleRawJetCLM P hp v hv hb 0 X.1).1)+
    -nativePositiveCollarRestrictionCLM ((∑j : Fin 3,nativePoissonCollarSecond P
      (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X) j j)+nativeCollarPotentialMulCLM P.potential
      (nativePoissonCollarValue P (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X)))=_
  rw [hh,hl,neg_zero,add_zero]

omit P hp v hv hb in
def nativeInteriorNativeJacobianCLM (g : RiemannianMetric 3 E) (r : ℝ) (V : ℝ→ᵇℝ) :
    NativeCollarJet →L[ℝ] Lp ℝ 2 (volume.restrict nativePositiveEntranceCollar) :=
  (8:ℝ) • nativePositiveCollarRestrictionCLM.comp (nativeFlatCollarJetCLM V+nativeBCFCollarErrorCLM g r V)

theorem nativeTwoSidedInterior_feedback_native_equation
    (hpot : P.potential=delaunayPhasePotentialBCF v hv hb 0)
    {t₀ : ℝ} (ht : 0<t₀) (g : RiemannianMetric 3 E) (r : ℝ)
    (hK : ‖nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht g r‖≤1/2) (X : NativeTwoSidedSource) :
    let Y := nativeTwoSidedFeedbackCLM (nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht g r) hK X
    nativeInteriorNativeJacobianCLM g r P.potential (nativeTwoSidedInteriorJetCLM P hp v hv hb t₀ Y).val=
      (-8:ℝ) • nativePositiveCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM X.1) := by
  dsimp only
  let Y := nativeTwoSidedFeedbackCLM (nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht g r) hK X
  have he := (nativeTwoSidedCollarFeedback_physical_identity P hp v hv hb ht g r hK X).1
  change nativeL2FullPhysicalSourceCLM Y.1=nativeL2FullPhysicalSourceCLM X.1+
    nativeTwoSidedInteriorErrorCLM P hp v hv hb (t₀:=t₀) g r Y at he
  simp only [nativeInteriorNativeJacobianCLM,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply,map_add,nativeTwoSidedInterior_flat_source P hp v hv hb hpot]
  change (8:ℝ) • (-nativePositiveCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM Y.1)+
    nativePositiveCollarRestrictionCLM (nativeTwoSidedInteriorErrorCLM P hp v hv hb (t₀:=t₀) g r Y))=_
  rw [he,map_add]
  module

omit P hp v hv hb in
theorem nativeInteriorNativeJacobian_weak_ae (g : RiemannianMetric 3 E) (r : ℝ)
    (V : ℝ→ᵇℝ) (J : nativeCollarJetClosure) :
    (nativeInteriorNativeJacobianCLM g r V J.val : E→ℝ)=ᵐ[volume.restrict nativePositiveEntranceCollar]
      (fun x => 8*weakNegativeLaplacian nativePoissonEntranceCollar J.val.1 x-
        8*weakSecondOrderPerturbation nativePoissonEntranceCollar (nativeScaledPrincipalError g r)
          (nativeScaledFirstError g r) (fun _ => 0) J.val.1 x+
        (8*r^2*nativePotentialDensity g (r • x)-
          8*g.pullbackVolumeDensity id (r • x)*nativeHalfEndPotentialCoefficient V x)*(J.val.1 : E→ℝ) x) := by
  let Z := nativeFlatCollarJetCLM V J.val+nativeBCFCollarErrorCLM g r V J.val
  have hμ : volume.restrict nativePositiveEntranceCollar≤volume.restrict nativePoissonEntranceCollar :=
    Measure.restrict_mono inter_subset_left le_rfl
  filter_upwards [Lp.coeFn_smul (8:ℝ) (nativePositiveCollarRestrictionCLM Z),nativePositiveCollarRestrictionCLM_ae Z,
    ae_mono hμ (Lp.coeFn_add (nativeFlatCollarJetCLM V J.val) (nativeBCFCollarErrorCLM g r V J.val)),
    ae_mono hμ (nativeFlatCollarJet_weak_ae V J),ae_mono hμ (nativeBCFCollarError_weak_ae g r V J)]
    with x hs hr ha hf he
  change ((8:ℝ) • nativePositiveCollarRestrictionCLM Z : Lp ℝ 2 (volume.restrict nativePositiveEntranceCollar)) x=_
  rw [hs]
  change 8*nativePositiveCollarRestrictionCLM Z x=_
  rw [hr]
  change 8*(nativeFlatCollarJetCLM V J.val+nativeBCFCollarErrorCLM g r V J.val : NativeCollarL2) x=_
  rw [ha]
  change 8*(nativeFlatCollarJetCLM V J.val x+nativeBCFCollarErrorCLM g r V J.val x)=_
  rw [hf,he]
  simp only [nativeBCFPotentialError]
  ring

#print axioms nativeTwoSidedInterior_flat_source
#print axioms nativeTwoSidedInterior_feedback_native_equation
#print axioms nativeInteriorNativeJacobian_weak_ae
end Yamabe3.Analysis.SpherePolar
