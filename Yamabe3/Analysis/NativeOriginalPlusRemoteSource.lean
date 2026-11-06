import Yamabe3.Analysis.NativeSmoothPotentialResponseEquation
import Yamabe3.Analysis.NativeOriginalAffineInnerSource
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


local notation "H" => H1Zero g.leviCivitaData univ
local notation "RH" => nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))

theorem nativeRemoteReturnResponse_inner_source_fixed (R₁:RH):
    let Y:=nativeOriginalAffineFeedbackCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH) R₁
    Y.val.1=nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb τ gE a Y.val:=by
  dsimp only
  let Y:=nativeOriginalAffineFeedbackCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH) R₁
  let Rt:=R₁+W.R Y
  have hh:=congrArg Prod.fst (nativeRemoteReturnResponse_fixed W R₁)
  change Y.val.1=nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb τ gE a Y.val-(W.I Rt).val.1 at hh
  have hz:(W.I Rt).val.1=0:=congrArg Prod.fst (W.incoming.2.1 Rt)
  simpa only [hz,sub_zero] using hh

theorem nativeOriginalPlusRemote_inner_source_fixed
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] RH) (x:HalfEndPhysicalH4Graph) (R₁:RH):
    let Y₀:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    let Y₁:=nativeOriginalAffineFeedbackCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH) R₁
    let Y:=Y₀+Y₁
    Y.val.1=nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp gE a x+
      nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb τ gE a Y.val:=by
  dsimp only
  have h0:=nativeOriginalAffineFeedback_inner_source_fixed W Rbase x
  have h1:=nativeRemoteReturnResponse_inner_source_fixed W R₁
  dsimp only at h0 h1
  change _+_= _+nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb τ gE a (_+_)
  rw [map_add,h0,h1]
  abel

theorem nativeOriginalPlusRemote_signed_identity
    (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H)
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] RH)
    (f:HalfEndPhysicalH2SourceGraph) (R₁:RH):
    let Y₀:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
    let Y₁:=nativeOriginalAffineFeedbackCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH) R₁
    let Y:=Y₀+Y₁
    nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f+nativeRemoteReturnResponseCLM W R₁=
      Q₀ f+nativeSupportedSignedEnergy W Y (Rbase (T₀ f)+R₁+W.R Y):=by
  dsimp only
  let Y₀:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
  let Y₁:=nativeOriginalAffineFeedbackCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH) R₁
  let C:=energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) W.core W.core.smooth
  change (Q₀ f+W.Q Y₀.val+C (Rbase (T₀ f)+W.R Y₀).val-(Rbase (T₀ f)+W.R Y₀).val)+
    (W.Q Y₁.val+C (R₁+W.R Y₁).val-(R₁+W.R Y₁).val)=
      Q₀ f+(W.Q (Y₀+Y₁).val+C (Rbase (T₀ f)+R₁+W.R (Y₀+Y₁)).val-(Rbase (T₀ f)+R₁+W.R (Y₀+Y₁)).val)
  simp only [Submodule.coe_add,map_add]
  abel

#print axioms nativeRemoteReturnResponse_inner_source_fixed
#print axioms nativeOriginalPlusRemote_inner_source_fixed
#print axioms nativeOriginalPlusRemote_signed_identity
end Yamabe3.Analysis.SpherePolar
