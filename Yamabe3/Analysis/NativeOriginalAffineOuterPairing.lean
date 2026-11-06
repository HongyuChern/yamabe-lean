import Yamabe3.Analysis.NativeFiniteWindowJacobianPairing
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


theorem nativeOriginalAffineFeedback_outer_residual_pairing
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (x:HalfEndPhysicalH4Graph) (G:Lp AngularSpectralSpace 2 (volume:Measure ℝ))
    (hG:∀ᵐt:ℝ∂volume,t∉Ioc (-(m:ℝ)/2) 0 →G t=0):
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    let R:=nativeOriginalAffineReturnCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    (∑i:Fin m,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      (nativeFiniteWindowOuterJacobianRow P hp v hv hb b ht gE a i Y.val)) G)+
      inner ℝ (nativeH4FiniteWindowGlobalSourceCLM P hp ht m gE a x).2 G=
    (∑i:Fin m,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      (nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y.val)) G)+
      inner ℝ (W.I R).val.2 G:=by
  dsimp only
  let B₀:=nativeActualH4BaselineResidualCLM W
  let Y:=nativeOriginalAffineFeedbackCLM W B₀ Rbase x
  let R:=nativeOriginalAffineReturnCLM W B₀ Rbase x
  let X':nativeSupportedSourcePairSpace b:=B₀ x-W.I R
  have hfix:Y.val=X'.val+nativeFiniteWindowGlobalSourceCLM P hp v hv hb b ht m gE a Y.val:=by
    have hh:=nativeOriginalAffineFeedback_fixed W B₀ Rbase x
    change Y.val=(B₀ x).val+_-(W.I R).val at hh
    change Y.val=((B₀ x).val-(W.I R).val)+_
    exact hh.trans (by abel)
  have hXs:= (nativeSupportedSourcePairSpace_mem_iff b X'.val).mp X'.property
  have hpairs:=nativeFiniteWindowOuter_fixed_pairing P hp v hv hb b ht m gE a X'.val Y.val
    hfix W.near_support hXs G hG
  have hx:X'.val.2=(nativeH4FiniteWindowGlobalSourceCLM P hp ht m gE a x).2-(W.I R).val.2:=rfl
  rw [hx,inner_sub_left] at hpairs
  linarith only [hpairs]

#print axioms nativeOriginalAffineFeedback_outer_residual_pairing
end Yamabe3.Analysis.SpherePolar
