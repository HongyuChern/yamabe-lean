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


 theorem nativeRemoteReturn_closed_jet_far_equation
    (Y:nativeSupportedSourcePairSpace b)
    (Rbase:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (F:Lp ℝ 2 g.volumeMeasure)
    (hbase:∀η:H1Zero g.leviCivitaData univ,
      closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const Rbase.val η=
        ∫y,(F y+8*(nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a)) y*
          toL2 g.leviCivitaData univ Rbase.val y))*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure)
    (η:H1Zero g.leviCivitaData univ):
    let R:=Rbase+W.R Y
    let J:ℝ→nativeCollarJetClosure:=nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val
    closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const R.val η=
      ∫y,(F y+nativeClosedJetFarSource g gE e (closedBall (0:E) R₀) a S
        (fun i:Fin n=>nativeOuterLogShellCenter (m+i.val))
        (nativeCollarCutoffCommutatorCLM χout hχout (J S).val)
        (fun i:Fin n=>nativeBCFCollarErrorCLM gE (a*Real.exp (-nativeOuterLogShellCenter (m+i.val)))
          (boundedTimeTranslate ℝ (nativeOuterLogShellCenter (m+i.val)) (fullBubblePhasePotential τ))
          (nativeCollarCutoffCLM (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter (m+i.val)) χout)
            (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter (m+i.val)) hχout)
            (J (nativeOuterLogShellCenter (m+i.val)))).val)
        (nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a))) R.val y)*
        toL2 g.leviCivitaData univ η y ∂g.volumeMeasure:=by
  dsimp only
  let J:ℝ→nativeCollarJetClosure:=nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val
  let t:Fin n→ℝ:=fun i=>nativeOuterLogShellCenter (m+i.val)
  let C:=nativeCollarCutoffCommutatorCLM χout hχout (J S).val
  let G:Fin n→NativeCollarL2:=fun i=>nativeBCFCollarErrorCLM gE (a*Real.exp (-t i))
    (boundedTimeTranslate ℝ (t i) (fullBubblePhasePotential τ))
    (nativeCollarCutoffCLM (nativeOuterFieldCutoffAtScale S (t i) χout)
      (nativeOuterFieldCutoffAtScale_smooth S (t i) hχout) (J (t i))).val
  let q:=nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a))
  let u₀:H1Zero g.leviCivitaData univ:=Rbase.val
  let u₁:H1Zero g.leviCivitaData univ:=(W.R Y).val
  let f₀:M→ℝ:=fun y=>F y+8*(q y*toL2 g.leviCivitaData univ u₀ y)
  let f₁:=nativeClosedJetFarSource g gE e (closedBall (0:E) R₀) a S t C G q u₁
  have hm₀:MemLp f₀ 2 g.volumeMeasure:=(Lp.memLp F).add
    ((nativeBubbleTail_product_memLp_two g e (isCompact_closedBall (0:E) R₀) τ cTail (Real.log a) (toL2 g.leviCivitaData univ u₀)).const_mul 8)
  have hm₁:MemLp f₁ 2 g.volumeMeasure:=nativeClosedJetFarSource_memLp_two g gE e he hei
    (isCompact_closedBall (0:E) R₀) hsource a S t C G τ cTail u₁
  have hw₀:∀ζ:H1Zero g.leviCivitaData univ,closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const u₀ ζ=
      ∫y,f₀ y*toL2 g.leviCivitaData univ ζ y ∂g.volumeMeasure:=hbase
  have hw₁:∀ζ:H1Zero g.leviCivitaData univ,closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const u₁ ζ=
      ∫y,f₁ y*toL2 g.leviCivitaData univ ζ y ∂g.volumeMeasure:=fun ζ=>nativeActualFeedback_far_closed_jet_equation W Y ζ
  have hweak:=nativeWholeWeakSource_equation_add g u₀ u₁ f₀ f₁ hm₀ hm₁ hw₀ hw₁ η
  have hval:(toL2 g.leviCivitaData univ (u₀+u₁):M→ℝ)=ᵐ[g.volumeMeasure]
      (fun y=>toL2 g.leviCivitaData univ u₀ y+toL2 g.leviCivitaData univ u₁ y):=by
    rw [map_add]
    exact Lp.coeFn_add _ _
  apply hweak.trans
  apply integral_congr_ae
  filter_upwards [hval] with y hy
  change (f₀ y+f₁ y)*toL2 g.leviCivitaData univ η y=
    (F y+nativeClosedJetFarSource g gE e (closedBall (0:E) R₀) a S t C G q (u₀+u₁) y)*
      toL2 g.leviCivitaData univ η y
  dsimp only [f₀,f₁,nativeClosedJetFarSource]
  rw [hy]
  ring

#print axioms nativeRemoteReturn_closed_jet_far_equation
end Yamabe3.Analysis.SpherePolar
