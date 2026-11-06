import Yamabe3.Analysis.NativeOriginalAffineFeedback
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


theorem nativeOriginalAffineFeedback_inner_source_fixed
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (x:HalfEndPhysicalH4Graph) :
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    Y.val.1=nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp gE a x+
      nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb τ gE a Y.val := by
  dsimp only
  let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
  let R:=nativeOriginalAffineReturnCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
  have hh:=congrArg Prod.fst (nativeOriginalAffineFeedback_fixed W (nativeActualH4BaselineResidualCLM W) Rbase x)
  change Y.val.1=nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp gE a x+
    nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb τ gE a Y.val-(W.I R).val.1 at hh
  have hI:=W.incoming.2.1 R
  have hzero:(W.I R).val.1=0:=congrArg Prod.fst hI
  simpa only [hzero,sub_zero] using hh

#print axioms nativeOriginalAffineFeedback_inner_source_fixed
end Yamabe3.Analysis.SpherePolar
