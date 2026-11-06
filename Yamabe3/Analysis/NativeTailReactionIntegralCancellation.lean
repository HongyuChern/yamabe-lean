import Yamabe3.Analysis.NativeSignedTailReactionCancellation
import Yamabe3.Analysis.NativeFixedFarL2Source

/-! The ACTUAL full-minus-tail reaction on the same completion element
has the expected integral cancellation. Both products are genuinely L2;
the core-tail disjointness is proved from the retained ordered radius. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
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

 theorem nativeActualFeedback_tail_full_integral_cancellation
    (hc:Real.log 128≤cTail) (R:H1Zero g.leviCivitaData univ) (η:EnergyTest g.leviCivitaData univ):
    let q:=nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a
    let qT:=nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a))
    (∫y,8*(qT y-q y)*(1-W.core y)*toL2 g.leviCivitaData univ R y*η y ∂g.volumeMeasure)-
      (∫y,8*(qT y*toL2 g.leviCivitaData univ R y)*η y ∂g.volumeMeasure)=
      -(∫y,8*q y*(1-W.core y)*toL2 g.leviCivitaData univ R y*η y ∂g.volumeMeasure):=by
  dsimp only
  let q:=nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a
  let qT:=nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a))
  let Rc:=energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) W.core W.core.smooth R
  let L:=toL2 g.leviCivitaData univ (R-Rc)
  have hL:(L:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>(1-W.core y)*toL2 g.leviCivitaData univ R y):=by
    have hsub:=Lp.coeFn_sub (toL2 g.leviCivitaData univ R) (toL2 g.leviCivitaData univ Rc)
    rw [←map_sub] at hsub
    filter_upwards [hsub,native_energyMulSmooth_toL2_ae g W.core W.core.smooth R] with y hy hc
    change L y=toL2 g.leviCivitaData univ R y-toL2 g.leviCivitaData univ Rc y at hy
    have hcPoint:toL2 g.leviCivitaData univ Rc y=W.core y*toL2 g.leviCivitaData univ R y:=hc
    linear_combination hy-hcPoint
  obtain ⟨C,hC,T,hT,hTa⟩:=exists_nativeFullBubble_bounded_L2_multiplier g e (isCompact_closedBall (0:E) R₀) τ a
  have hFull:MemLp (fun y=>q y*(1-W.core y)*toL2 g.leviCivitaData univ R y) 2 g.volumeMeasure:=by
    apply (Lp.memLp (T L)).ae_eq
    filter_upwards [hTa L,hL] with y hy hl
    rw [hy,hl]
    ring
  have hTail:MemLp (fun y=>qT y*toL2 g.leviCivitaData univ R y) 2 g.volumeMeasure:=
    nativeBubbleTail_product_memLp_two g e (isCompact_closedBall (0:E) R₀) τ cTail (Real.log a) _
  have htc:=nativeActualFeedback_tail_core_exclusion W hc
  have hpt(y:M):8*(qT y-q y)*(1-W.core y)*toL2 g.leviCivitaData univ R y=
      8*(qT y*toL2 g.leviCivitaData univ R y)-8*q y*(1-W.core y)*toL2 g.leviCivitaData univ R y:=by
    have hz:=congrArg (fun r:ℝ=>r*toL2 g.leviCivitaData univ R y) (htc y)
    simp only [zero_mul] at hz
    change qT y*W.core y*toL2 g.leviCivitaData univ R y=0 at hz
    linear_combination -8*hz
  have hiT:Integrable (fun y=>8*(qT y*toL2 g.leviCivitaData univ R y)*η y) g.volumeMeasure:=
    (hTail.const_mul 8).integrable_mul η.memLp
  have hiF:Integrable (fun y=>8*q y*(1-W.core y)*toL2 g.leviCivitaData univ R y*η y) g.volumeMeasure:=by
    convert (hFull.const_mul 8).integrable_mul η.memLp using 1
    congr 1
    funext y
    simp only [Pi.mul_apply]
    ring
  have he:(∫y,8*(qT y-q y)*(1-W.core y)*toL2 g.leviCivitaData univ R y*η y ∂g.volumeMeasure)=
      (∫y,8*(qT y*toL2 g.leviCivitaData univ R y)*η y ∂g.volumeMeasure)-
        (∫y,8*q y*(1-W.core y)*toL2 g.leviCivitaData univ R y*η y ∂g.volumeMeasure):=by
    calc
      _=(∫y,8*(qT y*toL2 g.leviCivitaData univ R y)*η y-
          8*q y*(1-W.core y)*toL2 g.leviCivitaData univ R y*η y ∂g.volumeMeasure):=by
        apply integral_congr_ae
        exact Eventually.of_forall (fun y=>
          (congrArg (fun r:ℝ=>r*(η:M→ℝ) y) (hpt y)).trans (sub_mul _ _ _))
      _=_:=integral_sub hiT hiF
  linarith only [he]

#print axioms nativeActualFeedback_tail_full_integral_cancellation
end Yamabe3.Analysis.SpherePolar
