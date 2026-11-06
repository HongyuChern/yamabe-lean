import Yamabe3.Analysis.NativeFullBubbleNativePotential
import Yamabe3.Analysis.NativeOriginalSignedEnergy

/-! The SAME signed completed field has the exact native full/tail
reaction cancellation. Core-tail disjointness is proved from the actual
ordered radius and genuine core support. This does not identify the
compact-chart potential with a different smooth paper truncation. -/
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


theorem nativeActualFeedback_tail_core_exclusion (hc:Real.log 128≤cTail):
    ∀y:M,nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a)) y*W.core y=0:=by
  rw [W.core_coordinate]
  exact nativeBubbleTail_core_product_zero e (closedBall (0:E) R₀) ha τ hc χin W.inner_support

theorem nativeOriginalSignedEnergy_same_potential_reaction
    (hc:Real.log 128≤cTail)
    (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero g.leviCivitaData univ)
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (f:HalfEndPhysicalH2SourceGraph):
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
    let R:=nativeOriginalAffineReturnCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
    let q:=nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a
    let qT:=nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a))
    (fun y=>q y*toL2 g.leviCivitaData univ (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f) y)=ᵐ[g.volumeMeasure]
    (fun y=>q y*(toL2 g.leviCivitaData univ (Q₀ f) y+toL2 g.leviCivitaData univ (W.Q Y.val) y)+
      (qT y-q y)*(1-W.core y)*toL2 g.leviCivitaData univ R.val y-qT y*toL2 g.leviCivitaData univ R.val y):=by
  dsimp only
  have htc:=nativeActualFeedback_tail_core_exclusion W hc
  filter_upwards [nativeOriginalSignedEnergyCLM_ae W T₀ Q₀ Rbase f] with y hy
  rw [hy]
  have hz:=congrArg (fun x:ℝ=>x*toL2 g.leviCivitaData univ
    (nativeOriginalAffineReturnCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)).val y) (htc y)
  linear_combination hz

#print axioms nativeActualFeedback_tail_core_exclusion
#print axioms nativeOriginalSignedEnergy_same_potential_reaction
end Yamabe3.Analysis.SpherePolar
