import Yamabe3.Analysis.NativeOriginalAffineFeedback
import Yamabe3.Analysis.NativeH4SupportedWindowSource

/-! The actual affine fixed equation cancels the COMPLETE source against
its finite near geometric rows on EVERY spectral test. No near-window
support hypothesis on the test is imposed or inferred. The same total
return remains on the right-hand side. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay PoincareMT.LeviCivitaData.Dirichlet
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


theorem nativeOriginalAffine_all_test_source_cancellation
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (x:HalfEndPhysicalH4Graph) (G:Lp AngularSpectralSpace 2 (volume:Measure ℝ)):
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    let R:=nativeOriginalAffineReturnCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    (-(inner ℝ Y.val.2 G)+
      (∑i:Fin m,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
        (nativeH4FiniteWindowGeometricRowCLM P ht gE a i x+
          nativeFiniteWindowGeometricRowCLM P hp v hv hb b ht gE a i Y.val)) G))=
      inner ℝ (W.I R).val.2 G:=by
  dsimp only
  have hh:=nativeOriginalAffineFeedback_fixed W (nativeActualH4BaselineResidualCLM W) Rbase x
  have hpair:=congrArg (fun X:NativeTwoSidedSource=>inner ℝ X.2 G) hh
  change inner ℝ _ G=inner ℝ ((_+_)-(W.I _).val.2) G at hpair
  rw [inner_sub_left,inner_add_left] at hpair
  change inner ℝ _ G=inner ℝ (nativeH4FiniteWindowGlobalSourceCLM P hp ht m gE a x).2 G+
    inner ℝ (nativeFiniteWindowGlobalSourceCLM P hp v hv hb b ht m gE a _).2 G-inner ℝ _ G at hpair
  simp only [nativeH4FiniteWindowGlobalSourceCLM,nativeFiniteWindowGlobalSourceCLM,
    nativeFiniteOuterWindowSourceCLM,ContinuousLinearMap.prod_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,sum_inner] at hpair
  simp only [map_add,inner_add_left,Finset.sum_add_distrib]
  linarith only [hpair]

#print axioms nativeOriginalAffine_all_test_source_cancellation
end Yamabe3.Analysis.SpherePolar
