import Yamabe3.Analysis.NativeActualFeedbackCollarIdentity
import Yamabe3.Analysis.NativeGeneralMetricGreenMatching
import Yamabe3.Analysis.NativeCollarNativeBoundaryPairing

/-! The SAME feedback source pair gives matched actual collar jets and
native-density Green cancellation for that field. The completed-field
volume identity is inherited explicitly; this is local interface evidence,
not the missing whole-exterior Data or quotient-conormal equation. -/
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

theorem nativeActualFeedback_Green_matching (X:nativeSupportedSourcePairSpace b)
    (ψ:E→ℝ) (hψ:ContDiff ℝ (⊤:ℕ∞) ψ) (hc:HasCompactSupport ψ)
    (hs:tsupport ψ⊆nativePoissonEntranceCollar) :
    let hψ2:=hψ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    8*nativeCollarGreenRegionCLM (ball (0:E) 1) isOpen_ball.measurableSet (nativeRescaledMetric gE a) ψ hψ2
      (nativeTwoSidedInteriorJetCLM P hp v hv hb τ (W.T X).val).val+
    8*nativeCollarGreenVolumeCLM (nativeRescaledMetric gE a) ψ hψ2
      (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht (W.T X).val 0).val=0 := by
  have hm:=nativeSupportedTwoSidedExteriorAllScale_matching P hp v hv hb b ht (W.T X).val
  exact nativeCollar_general_metric_Green_matching (nativeRescaledMetric gE a) _ _ hm.1 hm.2.1 ψ hψ hc hs

theorem nativeActualFeedback_normal_pair_matching (X:nativeSupportedSourcePairSpace b)
    (ψ:E→ℝ) (hψ:Continuous ψ) :
    nativeCollarNativeNormalPairCLM (nativeRescaledMetric gE a) ψ hψ
      (nativeTwoSidedInteriorJetCLM P hp v hv hb τ (W.T X).val)=
    nativeCollarNativeNormalPairCLM (nativeRescaledMetric gE a) ψ hψ
      (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht (W.T X).val 0) := by
  have hm:=nativeSupportedTwoSidedExteriorAllScale_matching P hp v hv hb b ht (W.T X).val
  change inner ℝ (nativeSphereWeightedTest (nativeRescaledMetric gE a) ψ hψ)
    (nativeCollarNormalTraceCLM _)=inner ℝ (nativeSphereWeightedTest (nativeRescaledMetric gE a) ψ hψ)
    (nativeCollarNormalTraceCLM _)
  rw [hm.2.1]

theorem nativeActualFeedback_native_area_normal_matching (X:nativeSupportedSourcePairSpace b)
    (hGauss:∀(θ:SpherePolar.S)(z:E),(nativeRescaledMetric gE a).inner (θ:E) (θ:E) z=inner ℝ (θ:E) z)
    (ψ:E→ℝ) (hψ:Continuous ψ) :
    (∫θ:SpherePolar.S,ψ (θ:E)*(nativeCollarNormalTraceCLM
      (nativeTwoSidedInteriorJetCLM P hp v hv hb τ (W.T X).val):SpherePolar.S→ℝ) θ
      ∂(GreenMass.NativeGaussSphereArea.gaussRadiusMetric (nativeRescaledMetric gE a) 1 (by norm_num)).volumeMeasure)=
    (∫θ:SpherePolar.S,ψ (θ:E)*(nativeCollarNormalTraceCLM
      (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht (W.T X).val 0):SpherePolar.S→ℝ) θ
      ∂(GreenMass.NativeGaussSphereArea.gaussRadiusMetric (nativeRescaledMetric gE a) 1 (by norm_num)).volumeMeasure) := by
  rw [←nativeCollarNativeNormalPair_eq_integral _ hGauss ψ hψ,←nativeCollarNativeNormalPair_eq_integral _ hGauss ψ hψ]
  exact nativeActualFeedback_normal_pair_matching W X ψ hψ

#print axioms nativeActualFeedback_Green_matching
#print axioms nativeActualFeedback_normal_pair_matching
#print axioms nativeActualFeedback_native_area_normal_matching
end Yamabe3.Analysis.SpherePolar
