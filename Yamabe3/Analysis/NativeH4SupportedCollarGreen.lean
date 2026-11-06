import Yamabe3.Analysis.NativeOriginalSignedCollarIdentity
import Yamabe3.Analysis.NativeOriginalModelEnergyRealization
import Yamabe3.Analysis.NativeActualFeedbackLocalGreen

/-! The same SIGNED original-source completed field agrees with the
sum of its actual baseline and correction on the entire physical collar.
The shared return cancels there by the actual core plateau. The literal
baseline/correction jets retain matching value and normal traces. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp BoundedContinuousFunction RealInnerProductSpace
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
variable {g:RiemannianMetric 3 M} {gE:RiemannianMetric 3 E} {e:OpenPartialHomeomorph E M}
  {he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source}
  {hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target}
  {R₀:ℝ} {hsource:closedBall (0:E) R₀⊆e.source}
  {P:NativeHighPotential}
  {hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ}
  {v:ℝ→ℝ} {hv:Continuous v} {hb:∀t,0 ≤ v t ∧ v t ≤ 1}
  {τ cTail:ℝ} {ht:0 < τ} {m n:ℕ} {b S CR CM:ℝ}
  {χin χout:E→ℝ} {hχin:ContDiff ℝ ∞ χin} {hχout:ContDiff ℝ ∞ χout}
  {a:ℝ} {ha:0 < a} {ha1:a ≤ 1}
  (W:NativeActualFeedbackEnergyBundle (g:=g) (gE:=gE) (e:=e) (he:=he) (hei:=hei)
    (R₀:=R₀) (hsource:=hsource) (P:=P) (hp:=hp) (v:=v) (hv:=hv) (hb:=hb)
    (τ:=τ) (ht:=ht) (cTail:=cTail) (m:=m) (n:=n) (b:=b) (S:=S) (CR:=CR) (CM:=CM)
    (χin:=χin) (χout:=χout) (hχin:=hχin) (hχout:=hχout) a ha ha1)


include W in
theorem nativeH4Supported_actual_Cauchy_and_Green
    (Y:nativeSupportedSourcePairSpace b)
    (x:HalfEndPhysicalH4Graph) (F:E→ℝ) (hF:ContDiffOn ℝ 2 F ({0}ᶜ:Set E))
    (hTF:EqOn (nativeH4GraphFunction x) F (closedBall (0:E) 4)):
    let J:=nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp nativeH4GraphZeroScale x+
      nativeTwoSidedInteriorJetCLM P hp v hv hb τ Y.val
    let K:=nativeH4MatchedExteriorAllScaleJet P ht x 0+
      nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val 0
    nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K ∧
      nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K ∧
      (∀(ψ:E→ℝ)(hψ:ContDiff ℝ (⊤:ℕ∞) ψ),HasCompactSupport ψ →tsupport ψ⊆nativePoissonEntranceCollar →
        let hψ2:=hψ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
        8*nativeCollarGreenRegionCLM (ball (0:E) 1) isOpen_ball.measurableSet (nativeRescaledMetric gE a) ψ hψ2 J.val+
          8*nativeCollarGreenVolumeCLM (nativeRescaledMetric gE a) ψ hψ2 K.val=0) ∧
      (∀(ψ:E→ℝ)(hψ:Continuous ψ),nativeCollarNativeNormalPairCLM (nativeRescaledMetric gE a) ψ hψ J=
        nativeCollarNativeNormalPairCLM (nativeRescaledMetric gE a) ψ hψ K):=by
  dsimp only
  let J:=nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp nativeH4GraphZeroScale x+
    nativeTwoSidedInteriorJetCLM P hp v hv hb τ Y.val
  let K:=nativeH4MatchedExteriorAllScaleJet P ht x 0+
    nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val 0
  have hbase:=nativeH4Matched_actual_matching P hp ht x (⟨F,hF⟩:nativeC2OffZero) hTF
  have hcorr:=nativeSupportedTwoSidedExteriorAllScale_matching P hp v hv hb b ht Y.val
  have hm:nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K ∧
      nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K:=by
    dsimp only [J,K]
    rw [map_add,map_add,map_add,map_add,nativeH4MatchedExteriorAllScale_zero]
    exact ⟨congrArg₂ (·+·) hbase.1 hcorr.1,congrArg₂ (·+·) hbase.2.1 hcorr.2.1⟩
  refine ⟨hm.1,hm.2,fun ψ hψ hc hs=>?_,fun ψ hψ=>?_⟩
  · exact nativeCollar_general_metric_Green_matching (nativeRescaledMetric gE a) J K hm.1 hm.2 ψ hψ hc hs
  · change inner ℝ (nativeSphereWeightedTest (nativeRescaledMetric gE a) ψ hψ) (nativeCollarNormalTraceCLM J)=
      inner ℝ (nativeSphereWeightedTest (nativeRescaledMetric gE a) ψ hψ) (nativeCollarNormalTraceCLM K)
    rw [hm.2]

#print axioms nativeH4Supported_actual_Cauchy_and_Green
end Yamabe3.Analysis.SpherePolar
