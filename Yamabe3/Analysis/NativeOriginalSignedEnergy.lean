import Yamabe3.Analysis.NativeOriginalSourceCoupledFeedback
import Yamabe3.Analysis.NativeOriginalSourceNativeEnergy
import Yamabe3.Analysis.NativeHomogeneousCoreEnergyBound

/-! One SIGNED original-source completed native energy field. The
original baseline, supported correction and shared homogeneous return
remain bound to one source. This file does not assert a full native PDE
or a global quotient-conormal identity until they are separately proved. -/
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


def nativeOriginalSignedEnergyCLM
    (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero g.leviCivitaData univ)
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))) :
    HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero g.leviCivitaData univ :=
  let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase
  let Qcorr:=W.Q.comp ((nativeSupportedSourcePairSpace b).subtypeL.comp (Y.comp T₀))
  let R:=((nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))).subtypeL.comp
    (nativeOriginalAffineReturnCLM W (nativeActualH4BaselineResidualCLM W) Rbase)).comp T₀
  nativeNegativeFeedbackEnergyCLM g W.core W.core.smooth (Q₀+Qcorr) (ContinuousLinearMap.id ℝ _) R

theorem nativeOriginalSignedEnergyCLM_ae
    (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero g.leviCivitaData univ)
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (f:HalfEndPhysicalH2SourceGraph) :
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase
    (toL2 g.leviCivitaData univ (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f):M→ℝ)=ᵐ[g.volumeMeasure]
      fun y=>toL2 g.leviCivitaData univ (Q₀ f) y+toL2 g.leviCivitaData univ (W.Q (Y (T₀ f)).val) y-
        (1-W.core y)*toL2 g.leviCivitaData univ
          (nativeOriginalAffineReturnCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)).val y := by
  dsimp only
  let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase
  let Qcorr:=W.Q.comp ((nativeSupportedSourcePairSpace b).subtypeL.comp (Y.comp T₀))
  let R:=((nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))).subtypeL.comp
    (nativeOriginalAffineReturnCLM W (nativeActualH4BaselineResidualCLM W) Rbase)).comp T₀
  have hh:=nativeNegativeFeedbackEnergyCLM_ae g W.core W.core.smooth (Q₀+Qcorr) (ContinuousLinearMap.id ℝ _) R f
  have hL:(toL2 g.leviCivitaData univ ((Q₀+Qcorr) f):M→ℝ)=ᵐ[g.volumeMeasure]
      fun y=>toL2 g.leviCivitaData univ (Q₀ f) y+toL2 g.leviCivitaData univ (W.Q (Y (T₀ f)).val) y := by
    change (toL2 g.leviCivitaData univ (Q₀ f+W.Q (Y (T₀ f)).val):M→ℝ)=ᵐ[g.volumeMeasure] _
    rw [map_add]
    exact Lp.coeFn_add _ _
  filter_upwards [hh,hL] with y hz hl
  change toL2 g.leviCivitaData univ (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f) y=
    toL2 g.leviCivitaData univ ((Q₀+Qcorr) f) y-(1-W.core y)*toL2 g.leviCivitaData univ (R f) y at hz
  exact hz.trans (congrArg (fun t:ℝ=>t-(1-W.core y)*toL2 g.leviCivitaData univ (R f) y) hl)

#print axioms nativeOriginalSignedEnergyCLM_ae
end Yamabe3.Analysis.SpherePolar
