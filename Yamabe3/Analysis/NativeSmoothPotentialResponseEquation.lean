import Yamabe3.Analysis.NativeRemoteWholeExteriorEquation
import Yamabe3.Analysis.NativeSupportedSignedEnergy
import Yamabe3.Analysis.NativeRemoteReturnResponse
import Yamabe3.Analysis.NativeSmoothBubbleReactionL2
import Yamabe3.Analysis.NativeSharedEnergyTailSolver
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
open scoped NNReal Manifold ContDiff Topology ENNReal lp BoundedContinuousFunction RealInnerProductSpace
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
private def remoteH1Normed:NormedSpace ℝ H:=inferInstance
attribute [local instance] remoteH1Normed



 theorem nativeRemoteResponse_supported_identity (Rbase:RH):
    let Y:=nativeOriginalAffineFeedbackCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH) Rbase
    nativeRemoteReturnResponseCLM W Rbase=nativeSupportedSignedEnergy W Y (Rbase+W.R Y):=rfl

 theorem exists_nativeSmoothPotential_actual_response_equation
    (hY:0<Target.yamabeConstant g)
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hfit:a*Real.exp (((m+n:ℕ):ℝ)/2+1)≤R₀)
    (hfitTail:a*(Real.exp cTail+1)≤R₀) (hcTail:Real.log 128≤cTail)
    (χ:E→ℝ) (hSm:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ (nativeScaledSmoothBubblePotential e τ a χ))
    (q:Lp ℝ (3/2:ℝ≥0∞) g.volumeMeasure)
    (hq:(q:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a y-
      nativeScaledSmoothBubblePotential e τ a χ y))
    (T:H →L[ℝ] RH)
    (hTw:∀z:H,∀η:H,closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const (T z).val η=
      ∫y,(nativeCriticalPotentialReactionCLM g hY q z y+
        8*(nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a)) y*
          toL2 g.leviCivitaData univ (T z).val y))*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure)
    (z:H):
    let Y:=nativeOriginalAffineFeedbackCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH) (T z)
    let Z:=nativeRemoteReturnResponseCLM W (T z)
    let Comp:ℕ→NativeCollarL2:=fun i=>nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y.val
    let U:Fin (m+n)→NativeCollarL2:=fun i=>nativeCollarScalarMulCLM
      (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χout)
      (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχout).continuous (Comp i)
    ∃C:Lp ℝ 2 g.volumeMeasure,
      (C:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>∑i:Fin (m+n),nativeDensityCorrectedChartSource gE e (closedBall (0:E) R₀)
        (nativePhysicalShellSource a (nativeOuterLogShellCenter i) (U i)) y) ∧
    ∃F:Lp ℝ 2 g.volumeMeasure,
      (F:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>C y+8*nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a y*
        toL2 g.leviCivitaData univ Z y-8*((nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a y-
          nativeScaledSmoothBubblePotential e τ a χ y)*toL2 g.leviCivitaData univ z y)) ∧
      (Z,F)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const (e '' closedBall (0:E) a)ᶜ ∧
      (Z,F)∈NativeWeakEllipticDataSpace g (e '' closedBall (0:E) a)ᶜ
        (nativeJacobianPotential g (fun _:M=>0)) (nativeJacobianPotential_smooth g contMDiff_const):=by
  dsimp only
  let Y:=nativeOriginalAffineFeedbackCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH) (T z)
  let R:=T z+W.R Y
  obtain ⟨Fsrc,hFsrc,hcrit⟩:=exists_nativeSmoothBubble_same_reaction_L2 g hY e (isCompact_closedBall (0:E) R₀) τ a χ hSm q hq z
  have hbase(η:H):closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const (T z).val η=
      ∫y,(Fsrc y+8*(nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a)) y*
        toL2 g.leviCivitaData univ (T z).val y))*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure:=by
    apply (hTw z η).trans
    apply integral_congr_ae
    exact hcrit.mono (fun y hy=>congrArg (fun r:ℝ=>(r+8*(nativeCompactChartFunction e (closedBall (0:E) R₀)
      (fullBubbleScaledTail τ cTail (Real.log a)) y*toL2 g.leviCivitaData univ (T z).val y))*toL2 g.leviCivitaData univ η y) hy)
  have hFix:=nativeRemoteReturnResponse_fixed W (T z)
  obtain ⟨C,hC,F,hF,hforced,hdata⟩:=exists_nativeRemote_signed_whole_exterior_equation W hcoeff hfit hfitTail hcTail
    Y (T z) Fsrc hFix hbase
  have hz:=nativeRemoteResponse_supported_identity W (T z)
  rw [←hz] at hF hforced hdata
  refine ⟨C,hC,F,?_,hforced,hdata⟩
  filter_upwards [hF,hFsrc] with y hy hsrc
  exact hy.trans (congrArg (fun r:ℝ=>C y+8*nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a y*
    toL2 g.leviCivitaData univ (nativeRemoteReturnResponseCLM W (T z)) y-r) hsrc)

#print axioms nativeRemoteResponse_supported_identity
#print axioms exists_nativeSmoothPotential_actual_response_equation
end Yamabe3.Analysis.SpherePolar
