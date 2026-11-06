import Yamabe3.Analysis.NativeSupportedOuterSameField
import Yamabe3.Analysis.NativeSupportedLowCompensationAllScale
import Yamabe3.Analysis.NativeExteriorShiftedEquation

/-! The same complete exterior field satisfies the original full-source
model equation on every true exterior scale. Finite compensation is the
computed Cauchy correction, with its actual physical source displayed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

 theorem nativeSupportedOuterAllScale_source (b : ℝ) {τ : ℝ} (ht : 0<τ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2)
    (σ : AngularH1) (hσ : NativeAngularSpectralRegular (3/2) (angularEmbedding σ))
    (hF : ∀ᵐt : ℝ ∂volume,t<b → F t=0) (s : ℝ) :
    (nativeNegativeScaledRestrictionCLM s
      (nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s (fullBubblePhasePotential τ))
        (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s).val) : E→ℝ)
      =ᵐ[volume.restrict (nativeNegativeScaledCollar s)]
      (fun x => -(nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F) : E→ℝ) x+
        nativeSupportedLowCompensationScaled b ht F d n s x) := by
  let V := boundedTimeTranslate ℝ s (fullBubblePhasePotential τ)
  let R := nativeNegativeScaledRestrictionCLM s
  let S := nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F)
  let C := nativeFlatCollarJetCLM V (nativeSupportedLowCauchyAllScaleJet b ht F d n s).val
  have hpart : nativeFlatCollarJetCLM V (nativeSupportedParticularJet τ b s F).val= -S :=
    nativeBubbleFullSupportedAllScale_equation τ b s F hF
  have hz (a : AngularH1) (ha : NativeAngularSpectralRegular (3/2) (angularEmbedding a)) :
      R (nativeFlatCollarJetCLM V (nativeExteriorShiftedJet (fullBubbleHighPotential (-τ)) s a ha).val)=0 := by
    have h := nativeExteriorShifted_flat_equation (fullBubbleHighPotential (-τ)) a ha s
    rw [nativeBubbleExteriorPotential_eq_phase] at h
    exact h
  have he : R (nativeFlatCollarJetCLM V (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s).val)= -R S+R C := by
    unfold nativeSupportedOuterAllScaleJet
    simp only [Submodule.coe_add,Submodule.coe_sub,map_add,map_sub,hpart,map_neg,hz,sub_zero,add_zero]
    rfl
  rw [he]
  have hμ : volume.restrict (nativeNegativeScaledCollar s)≤volume.restrict nativePoissonEntranceCollar :=
    Measure.restrict_mono inter_subset_left le_rfl
  have hR (U : NativeCollarL2) : (R U : E→ℝ)=ᵐ[volume.restrict (nativeNegativeScaledCollar s)] (U : E→ℝ) :=
    l2MeasureRestrict_ae hμ U
  have hc := ae_mono hμ (nativeSupportedLowCauchyAllScale_source b ht F d n s)
  filter_upwards [Lp.coeFn_add (-R S) (R C),Lp.coeFn_neg (R S),hR S,hR C,hc] with x ha hn hs hr hc
  rw [ha]
  change (-R S) x+R C x=_
  rw [hn]
  change -(R S x)+R C x=_
  rw [hs,hr]
  change -S x+C x=_
  change C x=nativeSupportedLowCompensationScaled b ht F d n s x at hc
  rw [hc]

#print axioms nativeSupportedOuterAllScale_source
end Yamabe3.Analysis.SpherePolar
