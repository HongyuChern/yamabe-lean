import Yamabe3.Analysis.NativeOuterShellEquationReturn

/-! The SAME exterior field satisfies the full-source shell equation,
including the ACTUAL four compensated low channels. The equation is used
only on its true exterior portion; the interface sphere is volume-null. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic

theorem nativeSupportedOuter_shell_model_source (b:ℝ) {τ:ℝ} (ht:0 < τ)
    (F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2)
    (σ:AngularH1) (hσ:NativeAngularSpectralRegular (3/2) (angularEmbedding σ))
    (hF:∀ᵐt:ℝ∂volume,t < b → F t=0) (k:ℕ) :
    let s:=nativeOuterLogShellCenter k
    let V:=boundedTimeTranslate ℝ s (fullBubblePhasePotential τ)
    nativeFullShellSourceReturnCLM s
      (nativeFlatCollarJetCLM V (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s).val)=
      -nativeFullShellSourceReturnCLM s
        (nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F))+
      nativeFullShellSourceReturnCLM s
        (nativeFlatCollarJetCLM V (nativeSupportedLowCauchyAllScaleJet b ht F d n s).val) := by
  let s:=nativeOuterLogShellCenter k
  let V:=boundedTimeTranslate ℝ s (fullBubblePhasePotential τ)
  let J:=nativeSupportedOuterAllScaleJet b ht F d n σ hσ s
  let C:=nativeFlatCollarJetCLM V (nativeSupportedLowCauchyAllScaleJet b ht F d n s).val
  let S:=nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F)
  let D:=nativeNegativeScaledCollar s
  let R:=nativeNegativeScaledRestrictionCLM s
  have hμ:volume.restrict D ≤ volume.restrict nativePoissonEntranceCollar :=
    Measure.restrict_mono inter_subset_left le_rfl
  have hsrc:=nativeSupportedOuterAllScale_source b ht F d n σ hσ hF s
  have hcomp:=ae_mono hμ (nativeSupportedLowCauchyAllScale_source b ht F d n s)
  have hr:(R (-S+C):E→ℝ)=ᵐ[volume.restrict D] ((-S+C:NativeCollarL2):E→ℝ) :=
    l2MeasureRestrict_ae hμ (-S+C)
  have he:R (nativeFlatCollarJetCLM V J.val)=R (-S+C) := by
    apply Lp.ext
    filter_upwards [hsrc,hcomp,hr,ae_mono hμ (Lp.coeFn_add (-S) C),
      ae_mono hμ (Lp.coeFn_neg S)] with x hs hc hr ha hn
    change R (nativeFlatCollarJetCLM V J.val) x= -S x+nativeSupportedLowCompensationScaled b ht F d n s x at hs
    change C x=nativeSupportedLowCompensationScaled b ht F d n s x at hc
    rw [hs,hr,ha]
    change _=(-S:NativeCollarL2) x+C x
    rw [hn]
    change _= -S x+C x
    rw [hc]
  dsimp only
  change nativeFullShellSourceReturnCLM s (nativeFlatCollarJetCLM V J.val)=
    -nativeFullShellSourceReturnCLM s S+nativeFullShellSourceReturnCLM s C
  rw [nativeFullShellSourceReturn_eq_of_negativeRestriction k _ _ he,map_add,map_neg]

#print axioms nativeSupportedOuter_shell_model_source
end Yamabe3.Analysis.SpherePolar
