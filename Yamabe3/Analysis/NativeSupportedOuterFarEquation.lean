import Yamabe3.Analysis.NativeSupportedOuterAllScaleEquation
import Yamabe3.Analysis.NativeFullCollarSourceSupport
import Yamabe3.Analysis.NativeSupportedReverseTranslation
import Yamabe3.Analysis.NativeOrbitWeakJacobian

/-! The same complete outer field has the homogeneous full-bubble equation
beyond the actual source and compensation supports. No source is discarded
inside its support. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay UniformElliptic

lemma bubbleCompensation_zero_of_le (i:AngularIndex) {t:ℝ} (ht:t≤-(3/2:ℝ)) :
    bubbleCompensation i t=0 := by
  have hz:bubbleCompensationCutoff t=0:=bubbleCompensationCutoff.zero_of_le_dist (by
    change (1/2:ℝ)≤dist t (-1)
    rw [Real.dist_eq,abs_of_nonpos (by linarith only [ht])]
    linarith only [ht])
  simp only [bubbleCompensation,hz,zero_mul]

theorem nativeNegativeScaledCollar_eq_of_far {s:ℝ} (hs:s≤-(1/2:ℝ)) :
    nativeNegativeScaledCollar s=nativePoissonEntranceCollar := by
  apply Set.Subset.antisymm inter_subset_left
  intro x hx
  refine ⟨hx,?_⟩
  exact (Real.exp_le_exp.mpr hs).trans_lt ((nativePolarTimeWindow_norm (1/2) x).mp hx).1

theorem nativeL2FullPhysicalSource_translate_far_zero (b s:ℝ)
    (F:Lp AngularSpectralSpace 2 (volume:Measure ℝ))
    (hF:∀ᵐt:ℝ ∂volume,t<b→F t=0) (hs:s≤b-1) :
    nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F)=0 := by
  apply nativeL2FullPhysicalSource_zero_of_time_zero
  filter_upwards [nativeL2_lower_support_translate b s F hF] with t ht
  intro htc
  exact ht (by linarith only [htc.2,hs])

theorem nativeSupportedLowCompensationScaled_far_zero (b:ℝ) {τ:ℝ} (ht:0<τ)
    (F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2)
    {s:ℝ} (hs:s≤-τ-2) {x:E} (hx:x∈nativePoissonEntranceCollar) :
    nativeSupportedLowCompensationScaled b ht F d n s x=0 := by
  let f:=finiteAngular nativeLowIndexFinset
    (fun i=>weightedTimeShift s (nativeSupportedLowCompensationCoefficients b ht F d n i))
  have hf:f (cylinderCoordinates ⟨x,hx.1⟩)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hz:bubbleCompensation i (τ+(-Real.log ‖x‖+s))=0:=
      bubbleCompensation_zero_of_le i (by linarith only [hx.2.2,hs])
    dsimp only [weightedTimeShift,nativeSupportedLowCompensationCoefficients,cylinderCoordinates,Prod.fst]
    rw [hz]
    ring
  have hl:cylinderLift f x=0 := by
    change cylinderLift f (⟨x,hx.1⟩:puncturedSpace)=0
    rw [cylinderLift_coe,puncturedCylinderLift,hf,mul_zero]
  change physicalForcing f x/8=0
  rw [physicalForcing,hl]
  ring

theorem nativeSupportedOuter_far_weakNegativeLaplacian (b:ℝ) {τ:ℝ} (ht:0<τ)
    (F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2)
    (σ:AngularH1) (hσ:NativeAngularSpectralRegular (3/2) (angularEmbedding σ))
    (hF:∀ᵐt:ℝ ∂volume,t<b→F t=0) {s:ℝ}
    (hs0:s≤-(1/2:ℝ)) (hsb:s≤b-1) (hsc:s≤-τ-2) :
    weakNegativeLaplacian nativePoissonEntranceCollar
      (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x=>nativeHalfEndPotentialCoefficient (boundedTimeTranslate ℝ s (fullBubblePhasePotential τ)) x*
        (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s).val.1 x) := by
  let V:=boundedTimeTranslate ℝ s (fullBubblePhasePotential τ)
  let J:=nativeSupportedOuterAllScaleJet b ht F d n σ hσ s
  let T:=nativeFlatCollarJetCLM V J.val
  have hsrc:=nativeSupportedOuterAllScale_source b ht F d n σ hσ hF s
  have hz:=nativeL2FullPhysicalSource_translate_far_zero b s F hF hsb
  rw [hz] at hsrc
  have he:nativeNegativeScaledCollar s=nativePoissonEntranceCollar:=nativeNegativeScaledCollar_eq_of_far hs0
  have hr:(nativeNegativeScaledRestrictionCLM s T:E→ℝ)=ᵐ[volume.restrict (nativeNegativeScaledCollar s)] (T:E→ℝ):=
    l2MeasureRestrict_ae (Measure.restrict_mono inter_subset_left le_rfl) T
  have ht':(T:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] (fun _=>0):=by
    have hμ:volume.restrict nativePoissonEntranceCollar≤volume.restrict (nativeNegativeScaledCollar s):=by rw [he]
    filter_upwards [ae_mono hμ hr,ae_mono hμ hsrc,Lp.coeFn_zero ℝ 2 (volume.restrict nativePoissonEntranceCollar),
      ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hr hx hz hxO
    change nativeNegativeScaledRestrictionCLM s T x=_ at hr
    rw [←hr]
    rw [hx,hz,nativeSupportedLowCompensationScaled_far_zero b ht F d n hsc hxO]
    simp only [Pi.zero_apply,neg_zero,add_zero]
  filter_upwards [ht',nativeFlatCollarJet_weak_ae V J] with x hz hx
  change T x=0 at hz
  change T x=_ at hx
  exact sub_eq_zero.mp (hx.symm.trans hz)

#print axioms bubbleCompensation_zero_of_le
#print axioms nativeNegativeScaledCollar_eq_of_far
#print axioms nativeL2FullPhysicalSource_translate_far_zero
#print axioms nativeSupportedLowCompensationScaled_far_zero
#print axioms nativeSupportedOuter_far_weakNegativeLaplacian
end Yamabe3.Analysis.SpherePolar
