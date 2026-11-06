import Yamabe3.Analysis.NativeShellEquationReturn
import Yamabe3.Analysis.NativeFullSourceReconstruction
import Yamabe3.Analysis.NativeFullDelaunayCollar

/-! Full source returns use only the positive-time region on which the
same high plus low physical field satisfies its equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeFullShellSourceReturn_eq_of_shell_ae (s : ℝ) (U W : NativeCollarL2)
    (he : (U : E → ℝ)=ᵐ[volume.restrict nativeSourceShell] (W : E → ℝ)) :
    nativeFullShellSourceReturnCLM s U=nativeFullShellSourceReturnCLM s W := by
  have hm : nativeShellSourceWeightCLM U=nativeShellSourceWeightCLM W := by
    apply Lp.ext
    have he' := ae_restrict_of_ae (s := nativePoissonEntranceCollar)
      ((ae_restrict_iff' nativeSourceShell_measurable).mp he)
    filter_upwards [nativeShellSourceWeightCLM_ae U,nativeShellSourceWeightCLM_ae W,he'] with x hu hw he
    rw [hu,hw]
    by_cases hx : x∈nativeSourceShell
    · rw [he hx]
    · simp only [nativeShellSourceWeight,indicator_of_notMem hx,zero_mul]
  simp only [nativeFullShellSourceReturnCLM,ContinuousLinearMap.comp_apply,hm]

theorem nativeFullShellSourceReturn_eq_of_positiveRestriction (n : ℕ) (U W : NativeCollarL2)
    (he : nativePositiveScaledRestrictionCLM (nativeLogShellCenter n) U=
      nativePositiveScaledRestrictionCLM (nativeLogShellCenter n) W) :
    nativeFullShellSourceReturnCLM (nativeLogShellCenter n) U=
      nativeFullShellSourceReturnCLM (nativeLogShellCenter n) W := by
  let D := nativePositiveScaledCollar (nativeLogShellCenter n)
  have hμ : volume.restrict D≤volume.restrict nativePoissonEntranceCollar :=
    Measure.restrict_mono inter_subset_left le_rfl
  have hU : (nativePositiveScaledRestrictionCLM (nativeLogShellCenter n) U : E → ℝ)=ᵐ[volume.restrict D] (U : E → ℝ) :=
    l2MeasureRestrict_ae hμ U
  have hW : (nativePositiveScaledRestrictionCLM (nativeLogShellCenter n) W : E → ℝ)=ᵐ[volume.restrict D] (W : E → ℝ) :=
    l2MeasureRestrict_ae hμ W
  rw [he] at hU
  apply nativeFullShellSourceReturn_eq_of_shell_ae
  exact ae_mono (Measure.restrict_mono (nativeSourceShell_subset_positiveScale n) le_rfl) (hU.symm.trans hW)

theorem nativeFullDelaunay_shell_equation {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (p : DelaunayPhaseData κ)
    (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ)
    (n : ℕ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
      ((∑ j : Fin 3,(nativeFullDelaunayRawJetCLM hκ0 hκ1 p hp (nativeLogShellCenter n) F).2.2 j j)+
        nativeCollarPotentialMulCLM
          (delaunayPhasePotentialBCF p.orbit p.smooth.continuous p.bounded (p.phase+nativeLogShellCenter n))
          (nativeFullDelaunayRawJetCLM hκ0 hκ1 p hp (nativeLogShellCenter n) F).1)=
    nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
      (nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace (nativeLogShellCenter n) F)) :=
  nativeFullShellSourceReturn_eq_of_positiveRestriction n _ _ (nativeFullDelaunay_physical_equation hκ0 hκ1 p hp _ F)

#print axioms nativeFullShellSourceReturn_eq_of_shell_ae
#print axioms nativeFullShellSourceReturn_eq_of_positiveRestriction
#print axioms nativeFullDelaunay_shell_equation
end Yamabe3.Analysis.SpherePolar
