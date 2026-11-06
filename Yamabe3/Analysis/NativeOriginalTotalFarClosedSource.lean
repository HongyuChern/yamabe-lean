import Yamabe3.Analysis.NativeFarClosedJetRealization
import Yamabe3.Analysis.NativeClosedJetFarSourceAlgebra
import Yamabe3.Analysis.NativeOriginalSourceCoupledFeedback

/-! The SAME total return has the exact combined closed-jet far source,
with all geometric rows and the same absorbed tail. Actual L2 source
bounds justify adding the two all-H1 weak equations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
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

 theorem nativeOriginalAffineReturn_closed_jet_far_equation
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (hfar:NativeH4BaselineFarRealization g gE e (closedBall (0:E) R₀) P ht a S cTail m n χout hχout Rbase)
    (x:HalfEndPhysicalH4Graph) (η:H1Zero g.leviCivitaData univ):
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    let R:=nativeOriginalAffineReturnCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    let J:ℝ→nativeCollarJetClosure:=fun s=>nativeH4MatchedExteriorAllScaleJet P ht x s+
      nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val s
    closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const R.val η=
      ∫y,nativeClosedJetFarSource g gE e (closedBall (0:E) R₀) a S
        (fun i:Fin n=>nativeOuterLogShellCenter (m+i.val))
        (nativeCollarCutoffCommutatorCLM χout hχout (J S).val)
        (fun i:Fin n=>nativeBCFCollarErrorCLM gE (a*Real.exp (-nativeOuterLogShellCenter (m+i.val)))
          (boundedTimeTranslate ℝ (nativeOuterLogShellCenter (m+i.val)) (fullBubblePhasePotential τ))
          (nativeCollarCutoffCLM (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter (m+i.val)) χout)
            (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter (m+i.val)) hχout)
            (J (nativeOuterLogShellCenter (m+i.val)))).val)
        (nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a))) R.val y*
        toL2 g.leviCivitaData univ η y ∂g.volumeMeasure:=by
  dsimp only
  let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
  let J₀:ℝ→nativeCollarJetClosure:=nativeH4MatchedExteriorAllScaleJet P ht x
  let J₁:ℝ→nativeCollarJetClosure:=nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val
  let t:Fin n→ℝ:=fun i=>nativeOuterLogShellCenter (m+i.val)
  let cut:ℝ→nativeCollarJetClosure→L[ℝ]nativeCollarJetClosure:=fun s=>nativeCollarCutoffCLM
    (nativeOuterFieldCutoffAtScale S s χout) (nativeOuterFieldCutoffAtScale_smooth S s hχout)
  let geo:ℝ→NativeCollarJet→L[ℝ]NativeCollarL2:=fun s=>nativeBCFCollarErrorCLM gE (a*Real.exp (-s))
    (boundedTimeTranslate ℝ s (fullBubblePhasePotential τ))
  let C₀:=nativeCollarCutoffCommutatorCLM χout hχout (J₀ S).val
  let C₁:=nativeCollarCutoffCommutatorCLM χout hχout (J₁ S).val
  let G₀:Fin n→NativeCollarL2:=fun i=>geo (t i) (cut (t i) (J₀ (t i))).val
  let G₁:Fin n→NativeCollarL2:=fun i=>geo (t i) (cut (t i) (J₁ (t i))).val
  let q:=nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a))
  let u₀: H1Zero g.leviCivitaData univ:=(Rbase x).val
  let u₁: H1Zero g.leviCivitaData univ:=(W.R Y).val
  let f₀:=nativeClosedJetFarSource g gE e (closedBall (0:E) R₀) a S t C₀ G₀ q u₀
  let f₁:=nativeClosedJetFarSource g gE e (closedBall (0:E) R₀) a S t C₁ G₁ q u₁
  have hm₀:MemLp f₀ 2 g.volumeMeasure:=nativeClosedJetFarSource_memLp_two g gE e he hei
    (isCompact_closedBall (0:E) R₀) hsource a S t C₀ G₀ τ cTail u₀
  have hm₁:MemLp f₁ 2 g.volumeMeasure:=nativeClosedJetFarSource_memLp_two g gE e he hei
    (isCompact_closedBall (0:E) R₀) hsource a S t C₁ G₁ τ cTail u₁
  have hw₀:∀ζ:H1Zero g.leviCivitaData univ,closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const u₀ ζ=
      ∫y,f₀ y*toL2 g.leviCivitaData univ ζ y ∂g.volumeMeasure:=fun ζ=>hfar x ζ
  have hw₁:∀ζ:H1Zero g.leviCivitaData univ,closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const u₁ ζ=
      ∫y,f₁ y*toL2 g.leviCivitaData univ ζ y ∂g.volumeMeasure:=fun ζ=>nativeActualFeedback_far_closed_jet_equation W Y ζ
  have hweak:=nativeWholeWeakSource_equation_add g u₀ u₁ f₀ f₁ hm₀ hm₁ hw₀ hw₁ η
  have hsum:=nativeClosedJetFarSource_add_ae g gE e he hei (K:=closedBall (0:E) R₀) measurableSet_closedBall
    a S t C₀ C₁ G₀ G₁ q u₀ u₁
  have hC:nativeCollarCutoffCommutatorCLM χout hχout (J₀ S+J₁ S).val=C₀+C₁:=by
    simp only [Submodule.coe_add,map_add]
    rfl
  have hG:(fun i:Fin n=>geo (t i) (cut (t i) (J₀ (t i)+J₁ (t i))).val)=G₀+G₁:=by
    funext i
    change geo (t i) (cut (t i) (J₀ (t i)+J₁ (t i))).val=
      geo (t i) (cut (t i) (J₀ (t i))).val+geo (t i) (cut (t i) (J₁ (t i))).val
    rw [map_add,Submodule.coe_add,map_add]
  change closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const (u₀+u₁) η=
    ∫y,nativeClosedJetFarSource g gE e (closedBall (0:E) R₀) a S t
      (nativeCollarCutoffCommutatorCLM χout hχout (J₀ S+J₁ S).val)
      (fun i:Fin n=>geo (t i) (cut (t i) (J₀ (t i)+J₁ (t i))).val) q (u₀+u₁) y*
      toL2 g.leviCivitaData univ η y ∂g.volumeMeasure
  rw [hC,hG]
  apply hweak.trans
  apply integral_congr_ae
  filter_upwards [hsum] with y hy
  exact congrArg (fun r:ℝ=>r*toL2 g.leviCivitaData univ η y) hy.symm

#print axioms nativeOriginalAffineReturn_closed_jet_far_equation
end Yamabe3.Analysis.SpherePolar
