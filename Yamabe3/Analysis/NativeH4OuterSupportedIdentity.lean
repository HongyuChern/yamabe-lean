import Yamabe3.Analysis.NativeH4MatchedExteriorAllScale
import Yamabe3.Analysis.NativeSupportedOuterAllScaleEquation
import Yamabe3.Analysis.NativeSupportedOuterNewtonAnnulus

/-! The original H4 outer field is exactly the actual support-aware
exterior producer with ZERO outer forcing and its computed Cauchy data.
This identity retains the four compensations and makes the true
far-field regularity available without treating an H4 extension as the
outer PDE solution. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic

theorem nativeFiniteAllScaleJet_congr (m:Finset AngularIndex) (q₁ q₂:AngularIndex→ℝ→ℝ)
    (h₁:∀i∈m,ContDiff ℝ 2 (q₁ i)) (h₂:∀i∈m,ContDiff ℝ 2 (q₂ i))
    (h:q₁=q₂) (s:ℝ) : nativeFiniteAllScaleJet m q₁ h₁ s=nativeFiniteAllScaleJet m q₂ h₂ s := by
  subst q₂
  rfl

theorem nativeExteriorShiftedJet_zero (P:NativeHighPotential) (s:ℝ)
    (h0:NativeAngularSpectralRegular (3/2) (angularEmbedding (0:AngularH1))) :
    nativeExteriorShiftedJet P s 0 h0=0 := by
  let T:ℝ →L[ℝ] AngularH1:=0
  have hT:∀x:ℝ,NativeAngularSpectralRegular (3/2) (angularEmbedding (T x)):=fun _=>h0
  exact (nativeExteriorShiftedFamilyJetLinear P T hT s).map_zero

theorem nativeH4MatchedExteriorAllScale_supported_zero
    (P:NativeHighPotential) {τ:ℝ} (ht:0 < τ) (b:ℝ) (x:HalfEndPhysicalH4Graph) (s:ℝ) :
    nativeH4MatchedExteriorAllScaleJet P ht x s=
      nativeSupportedOuterAllScaleJet b ht 0 (nativeH4GraphAngularValueCLM x)
        (nativeH4GraphAngularNormalCLM x)
        (nativeH4GraphExteriorDatumCLM (fullBubbleHighPotential (-τ)) P x)
        (nativeH4GraphExteriorDatum_regular (fullBubbleHighPotential (-τ)) P x) s := by
  have hzero:NativeAngularSpectralRegular (3/2) (angularEmbedding (0:AngularH1)):=by
    simpa only [map_zero] using nativeH4GraphExteriorDatum_regular (fullBubbleHighPotential (-τ)) P (0:HalfEndPhysicalH4Graph)
  unfold nativeSupportedOuterAllScaleJet nativeSupportedParticularJet
  have hz:nativeL2EntranceH1 (fullBubbleHighPotential τ).κ_nonneg (fullBubbleHighPotential τ).κ_lt_one
      (fullBubblePhasePotential τ) (fullBubbleHighPotential τ).kernel_bound
      (fullBubblePhasePotential_plus_kernel τ) 0=0:=
    (nativeL2EntranceH1CLM (fullBubbleHighPotential τ).κ_nonneg (fullBubbleHighPotential τ).κ_lt_one
      (fullBubblePhasePotential τ) (fullBubbleHighPotential τ).kernel_bound
      (fullBubblePhasePotential_plus_kernel τ)).map_zero
  simp only [hz,map_zero,zero_add,add_zero,nativeExteriorShiftedJet_zero _ _ hzero,sub_zero]
  unfold nativeH4MatchedExteriorAllScaleJet nativeSupportedLowCauchyAllScaleJet nativeLowCauchyAllScaleJet
  have hdata:nativeBubbleLowCorrectionDataCLM τ (0,(nativeH4GraphAngularValueCLM x,nativeH4GraphAngularNormalCLM x))=
      (nativeH4GraphAngularValueCLM x,-nativeH4GraphAngularNormalCLM x-(1/2:ℝ) • nativeH4GraphAngularValueCLM x):=by
    change (nativeH4GraphAngularValueCLM x-nativeBubbleLowEntranceCLM τ 0,
      nativeBubbleLowNormalCLM τ 0-nativeH4GraphAngularNormalCLM x-
        (1/2:ℝ) • (nativeH4GraphAngularValueCLM x-nativeBubbleLowEntranceCLM τ 0))=_
    simp only [map_zero,sub_zero,zero_sub]
  have hq:nativeSupportedLowCauchyCoefficients b ht 0 (nativeH4GraphAngularValueCLM x)
      (nativeH4GraphAngularNormalCLM x)=
      fun i t=>nativeLowCauchyQ ht (nativeH4GraphLowCauchyCoordinateCLM x) i (τ+t):=by
    funext i t
    unfold nativeSupportedLowCauchyCoefficients
    simp only [map_zero,hdata]
    rfl
  exact congrArg (fun J:nativeCollarJetClosure=>J+
    nativeExteriorShiftedJet (fullBubbleHighPotential (-τ)) s
      (nativeH4GraphExteriorDatumCLM (fullBubbleHighPotential (-τ)) P x)
      (nativeH4GraphExteriorDatum_regular (fullBubbleHighPotential (-τ)) P x))
    (nativeFiniteAllScaleJet_congr _ _ _ _ _ hq.symm s)

#print axioms nativeExteriorShiftedJet_zero
#print axioms nativeH4MatchedExteriorAllScale_supported_zero
end Yamabe3.Analysis.SpherePolar
