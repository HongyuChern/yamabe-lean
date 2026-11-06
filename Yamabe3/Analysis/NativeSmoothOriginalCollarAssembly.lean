import Yamabe3.Analysis.NativeBaselineSupportedGluedRepresentation
import Yamabe3.Analysis.NativeH4SupportedCollarGreen
import Yamabe3.Analysis.NativeLocalH2ChartSource
import Yamabe3.Analysis.NativeOriginalPlusRemoteSource
import Yamabe3.Analysis.NativeScaledInnerWeakEquation
import Yamabe3.Analysis.NativeOriginalSupportedInnerSource
import Yamabe3.Analysis.NativeH4ValueInnerEquation
import Yamabe3.Analysis.NativeBaselineSupportedIdentity
import Yamabe3.Analysis.NativeOriginalAffineOriginalSource
import Yamabe3.Analysis.NativeOriginalSignedInnerIdentity
import Yamabe3.Analysis.NativeOriginalModelEnergyRealization
import Yamabe3.Analysis.NativeWeightedFieldPotentialL2
import Yamabe3.Analysis.NativeH4InnerPartialFeedback
import Yamabe3.Analysis.NativeH4SupportedWindowSource

/-! The ACTUAL affine original-source feedback has the required inner
fixed point, since its incoming source has exactly zero first coordinate.
This discharges the partial inner cancellation premise without assuming
an obsolete full-collar exterior fixed point. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp BoundedContinuousFunction RealInnerProductSpace
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
variable {g:RiemannianMetric 3 M} {gE:RiemannianMetric 3 E} {e:OpenPartialHomeomorph E M}
  {he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source}
  {hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target}
  {R₀:ℝ} {hsource:closedBall (0:E) R₀⊆e.source}
variable {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1) (p:DelaunayPhaseData κ)
  (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ)
local notation "P" => p.nativeHighPotential hκ0 hκ1
local notation "v" => (fun t=>p.orbit (t+p.phase))
local notation "hv" => (p.smooth.continuous.comp (continuous_id.add continuous_const))
local notation "hb" => (fun t=>p.bounded (t+p.phase))
variable   {τ cTail:ℝ} {ht:0 < τ} {m n:ℕ} {b S CR CM:ℝ}
  {χin χout:E→ℝ} {hχin:ContDiff ℝ ∞ χin} {hχout:ContDiff ℝ ∞ χout}
  {a:ℝ} {ha:0 < a} {ha1:a ≤ 1}
  (W:NativeActualFeedbackEnergyBundle g gE e he hei R₀ hsource
    (p.nativeHighPotential hκ0 hκ1) hp (fun t=>p.orbit (t+p.phase))
    (p.smooth.continuous.comp (continuous_id.add continuous_const))
    (fun t=>p.bounded (t+p.phase)) τ cTail ht m n b S CR CM χin χout hχin hχout a ha ha1)


local notation "H" => H1Zero g.leviCivitaData univ
local notation "RH" => nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))

theorem nativeSmoothOriginal_same_collar_realization
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (O:Set E) (L₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero nativeWeakEuclideanD O)
    (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H)
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] RH)
    (hModel:NativeOriginalModelEnergyRealization hκ0 hκ1 p hp ht χout S O T₀ L₀)
    (hQ₀:∀f,toL2 g.leviCivitaData univ (Q₀ f)=nativeCompactChartL2CLM g e he hei
      (isCompact_closedBall (0:E) R₀) hsource
      (euclideanL2DilationCLM ha ha1 (toL2 nativeWeakEuclideanD O (L₀ f))))
    (T:H →L[ℝ] RH) (JSm:H →L[ℝ] H)
    (hJSm:∀z:H,JSm z=z+nativeRemoteReturnResponseCLM W (T (JSm z)))
    (f:HalfEndPhysicalH2SourceGraph):
    let Z:=JSm (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f)
    let Y₀:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
    let Y₁:=nativeOriginalAffineFeedbackCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH) (T Z)
    let Y:=Y₀+Y₁
    let J:=nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp nativeH4GraphZeroScale (T₀ f)+
      nativeTwoSidedInteriorJetCLM P hp v hv hb τ Y.val
    let K:=nativeH4MatchedExteriorAllScaleJet P ht (T₀ f) 0+
      nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val 0
    (toL2 g.leviCivitaData univ Z:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' euclideanDilatedDomain a nativePoissonEntranceCollar)]
      coordinateExtension e (fun x:E=>nativeCollarGluedFunction J.val.1 K.val.1 (a⁻¹ • x)) ∧
    nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K ∧
    nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K ∧
    (∀(ψ:E→ℝ)(hψ:ContDiff ℝ (⊤:ℕ∞) ψ),HasCompactSupport ψ →tsupport ψ⊆nativePoissonEntranceCollar →
      let hψ2:=hψ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      8*nativeCollarGreenRegionCLM (ball (0:E) 1) isOpen_ball.measurableSet (nativeRescaledMetric gE a) ψ hψ2 J.val+
        8*nativeCollarGreenVolumeCLM (nativeRescaledMetric gE a) ψ hψ2 K.val=0) ∧
    (∀(ψ:E→ℝ)(hψ:Continuous ψ),nativeCollarNativeNormalPairCLM (nativeRescaledMetric gE a) ψ hψ J=
      nativeCollarNativeNormalPairCLM (nativeRescaledMetric gE a) ψ hψ K) ∧
    ∀y∈e '' euclideanDilatedDomain a nativePoissonEntranceCollar,
      ∃U:Set M,IsOpen U ∧ y∈U ∧ U⊆e '' euclideanDilatedDomain a nativePoissonEntranceCollar ∧
        ∃G:Lp ℝ 2 g.volumeMeasure,(Z,G)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const U:=by
  dsimp only
  let Z₀:=nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f
  let Z:=JSm Z₀
  let Y₀:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
  let Y₁:=nativeOriginalAffineFeedbackCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH) (T Z)
  let Y:=Y₀+Y₁
  let R:=Rbase (T₀ f)+T Z+W.R Y
  let J:=nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp nativeH4GraphZeroScale (T₀ f)+
    nativeTwoSidedInteriorJetCLM P hp v hv hb τ Y.val
  let K:=nativeH4MatchedExteriorAllScaleJet P ht (T₀ f) 0+
    nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val 0
  have hZ:Z=Q₀ f+nativeSupportedSignedEnergy W Y R:=
    (hJSm Z₀).trans (nativeOriginalPlusRemote_signed_identity W T₀ Q₀ Rbase f (T Z))
  obtain ⟨F,hF,hTF,hFa,qi,wo,hqi,hwo,hbi,hbo,hLE⟩:=hModel f
  have hBi:((nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp nativeH4GraphZeroScale (T₀ f)).val.1:E→ℝ)
      =ᵐ[volume.restrict nativePoissonEntranceCollar]fun x=>F x+cylinderLift qi x:=by
    simpa only [nativeH4GraphZeroScale,mul_zero,zero_div,Real.exp_zero,neg_zero,one_smul,one_mul] using hbi nativeH4GraphZeroScale
  have hBo:((nativeH4MatchedExteriorAllScaleJet P ht (T₀ f) 0).val.1:E→ℝ)
      =ᵐ[volume.restrict nativePoissonEntranceCollar]cylinderLift wo:=by
    simpa only [NativeScaledJetRep,mul_zero,zero_div,Real.exp_zero,neg_zero,one_smul,one_mul] using hbo 0
  obtain ⟨hrep,hm⟩:=nativeBaselineSupportedSigned_glued_representation W T₀ Q₀ Y R O L₀ hQ₀ f F hF hTF qi wo hLE hBi hBo
  rw [←hZ] at hrep
  have hGreen:=nativeH4Supported_actual_Cauchy_and_Green W Y (T₀ f) F hF hTF
  refine ⟨hrep,hm.1,hm.2,hGreen.2.2.1,hGreen.2.2.2,?_⟩
  let u:E→ℝ:=fun x=>nativeCollarGluedFunction J.val.1 K.val.1 (a⁻¹ • x)
  have hum:Measurable u:=
    ((Lp.stronglyMeasurable J.val.1).measurable.piecewise isOpen_ball.measurableSet
      (Lp.stronglyMeasurable K.val.1).measurable).comp (continuous_const_smul a⁻¹).measurable
  have hu:MemWkpLocally 2 u (euclideanDilatedDomain a nativePoissonEntranceCollar):=
    memWkpLocally_comp_dilation (inv_ne_zero ha.ne') (nativeCollarGluedFunction_local_H2 J K hm.1 hm.2)
  exact nativeLocalH2_chart_source g gE e he hei (isCompact_closedBall (0:E) R₀) hsource hcoeff
    ((nativePolarTimeWindow_open (1/2)).preimage (continuous_const_smul a⁻¹))
    (nativeActualFeedback_collar_fit W) u hum hu Z hrep

#print axioms nativeSmoothOriginal_same_collar_realization
end Yamabe3.Analysis.SpherePolar
