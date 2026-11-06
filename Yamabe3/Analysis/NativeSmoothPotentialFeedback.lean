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


private instance smoothFeedback32:Fact (1≤(3/2:ℝ≥0∞)):=
  ⟨(ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr (by norm_num)⟩
private instance smoothFeedback65:Fact (1≤(6/5:ℝ≥0∞)):=⟨one_le_sixFifths⟩

 theorem exists_nativeSmoothPotential_energy_feedback
    (hY:0<Target.yamabeConstant g)
    {N CI Ccore:ℝ} (hN:0≤N) (hCI:0≤CI) (hCM:0≤CM) (hCR:0≤CR) (hCore:0≤Ccore)
    (hI:‖W.I‖≤CI*Real.exp (-Real.log a/2))
    (hcore:∀R:RH,‖energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ)
      W.core W.core.smooth R.val‖≤Ccore*‖R‖)
    (hreceiver:NativeEnergyReceivingTailSolver g e (closedBall (0:E) R₀) τ 64 cTail N)
    {L:ℝ} (hL:(64:ℝ)≤L) (χ:E→ℝ) (hχone:∀x∈closedBall (0:E) L,χ x=1)
    (hs:tsupport (fun x:E=>χ (a⁻¹ • x))⊆closedBall (0:E) R₀)
    (hBallK:closedBall (0:E) (a*L)⊆closedBall (0:E) R₀)
    (q:Lp ℝ (3/2:ℝ≥0∞) g.volumeMeasure)
    (hq:(q:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a y-
      nativeScaledSmoothBubblePotential e τ a χ y))
    (hsmall:(4*CM*CI+(Ccore+1)*(1+4*CR*CI))*N*((8*‖GreenMass.NativeEnergyL6.toL6 g hY‖)*‖q‖)≤(1/2:ℝ)):
    ∃T:H →L[ℝ] RH,
      ‖T‖≤N*((8*‖GreenMass.NativeEnergyL6.toL6 g hY‖)*‖q‖) ∧
      (∀z:H,∀η:H,closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const (T z).val η=
        ∫y,(nativeCriticalPotentialReactionCLM g hY q z y+
          8*(nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a)) y*
            toL2 g.leviCivitaData univ (T z).val y))*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure) ∧
    ∃J:H →L[ℝ] H,‖J‖≤2 ∧ ∀z:H,J z=z+nativeRemoteReturnResponseCLM W (T (J z)):=by
  let A:=nativeCriticalPotentialReactionCLM g hY q
  have hsrc:ball (0:E) (a*64)⊆e.source:=ball_subset_closedBall.trans
    ((closedBall_subset_closedBall W.receiving_fit).trans hsource)
  have hz:=nativeSmoothBubble_reaction_zero_on_receiving_ball g hY e hsource τ ha hL χ hχone hs hBallK q hq
  have hzeroSmall:60*(∫y,|(0:ℝ)|^6 ∂g.volumeMeasure)^(2/3:ℝ)≤Target.yamabeConstant g:=by simpa using hY.le
  obtain ⟨T,hT,hTw⟩:=hreceiver (fun _:M=>0) contMDiff_const hzeroSmall a ha hsrc A hz
  have hTbound:‖T‖≤N*((8*‖GreenMass.NativeEnergyL6.toL6 g hY‖)*‖q‖):=
    hT.trans (mul_le_mul_of_nonneg_left (nativeCriticalPotentialReactionCLM_norm g hY q) hN)
  let C:=4*CM*CI+(Ccore+1)*(1+4*CR*CI)
  have hC:0≤C:=by dsimp only [C];positivity
  have hResp:‖nativeRemoteReturnResponseCLM W‖≤C:=nativeRemoteReturnResponse_uniform_bound W hCI hCM hCR hCore hI hcore
  let K:H →L[ℝ] H:=(nativeRemoteReturnResponseCLM W).comp T
  have hK:‖K‖≤(1/2:ℝ):=by
    calc
      _≤‖nativeRemoteReturnResponseCLM W‖*‖T‖:=ContinuousLinearMap.opNorm_comp_le _ _
      _≤C*(N*((8*‖GreenMass.NativeEnergyL6.toL6 g hY‖)*‖q‖)):=
        mul_le_mul hResp hTbound T.opNorm_nonneg hC
      _=(4*CM*CI+(Ccore+1)*(1+4*CR*CI))*N*((8*‖GreenMass.NativeEnergyL6.toL6 g hY‖)*‖q‖):=by dsimp only [C];ring
      _≤1/2:=hsmall
  let Id:=ContinuousLinearMap.id ℝ H
  have hId:‖Id‖≤1:=Id.opNorm_le_bound (by norm_num) (fun z=>by simp only [Id,ContinuousLinearMap.id_apply,one_mul];exact le_rfl)
  have hProd:‖Id‖*‖K‖≤(1/2:ℝ):=by
    calc
      _≤1*‖K‖:=mul_le_mul_of_nonneg_right hId (norm_nonneg _)
      _=‖K‖:=one_mul _
      _≤1/2:=hK
  let J:=strictFeedbackCLM Id K (q:=(1/2:ℝ≥0)) (by norm_num) hProd
  have hJ:‖J‖≤2:=by
    have hj:=strictFeedbackCLM_norm Id K (q:=(1/2:ℝ≥0)) (by norm_num) hProd
    norm_num at hj
    exact hj.trans (by nlinarith only [hId])
  refine ⟨T,hTbound,hTw,J,hJ,fun z=>?_⟩
  have hh:=strictFeedback_fixed Id K (q:=(1/2:ℝ≥0)) (by norm_num) hProd z
  exact hh.symm

#print axioms exists_nativeSmoothPotential_energy_feedback
end Yamabe3.Analysis.SpherePolar
