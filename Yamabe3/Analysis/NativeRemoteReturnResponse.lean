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


local notation "H" => H1Zero g.leviCivitaData univ
local notation "RH" => nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))
private def remoteH1Normed:NormedSpace ℝ H:=inferInstance
attribute [local instance] remoteH1Normed

def nativeRemoteReturnResponseCLM:RH →L[ℝ] H:=
  let Y:=nativeOriginalAffineFeedbackCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH)
  let Rt:=nativeOriginalAffineReturnCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH)
  nativeNegativeFeedbackEnergyCLM g W.core W.core.smooth
    (W.Q.comp ((nativeSupportedSourcePairSpace b).subtypeL.comp Y)) (ContinuousLinearMap.id ℝ RH)
    ((nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))).subtypeL.comp Rt)

 theorem nativeRemoteReturnResponse_fixed (R₀:RH):
    let Y:=nativeOriginalAffineFeedbackCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH) R₀
    let Rt:=R₀+W.R Y
    Y.val=nativeFiniteWindowGlobalSourceCLM P hp v hv hb b ht m gE a Y.val-(W.I Rt).val:=by
  have hh:=nativeOriginalAffineFeedback_fixed W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b)
    (ContinuousLinearMap.id ℝ RH) R₀
  simpa only [ContinuousLinearMap.zero_apply,ZeroMemClass.coe_zero,zero_add,nativeOriginalAffineReturnCLM,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using hh

 theorem nativeRemoteReturnResponse_uniform_bound
    {CI Ccore:ℝ} (hCI:0≤CI) (hCM:0≤CM) (hCR:0≤CR) (hCore:0≤Ccore)
    (hI:‖W.I‖≤CI*Real.exp (-Real.log a/2))
    (hcore:∀R:RH,‖energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ)
      W.core W.core.smooth R.val‖≤Ccore*‖R‖):
    ‖nativeRemoteReturnResponseCLM W‖≤4*CM*CI+(Ccore+1)*(1+4*CR*CI):=by
  let Y:=nativeOriginalAffineFeedbackCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH)
  let Rt:=nativeOriginalAffineReturnCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH)
  have hYnorm:‖Y‖≤4*‖W.I‖:=by
    apply Y.opNorm_le_bound (by positivity)
    intro R₀
    change ‖W.T (0-W.I R₀)‖≤_
    rw [zero_sub,map_neg,norm_neg]
    exact (W.T.le_of_opNorm_le W.feedback_bound _).trans
      ((mul_le_mul_of_nonneg_left (W.I.le_opNorm R₀) (by norm_num:(0:ℝ)≤4)).trans_eq (by ring))
  have hScale:Real.sqrt a*Real.exp (-Real.log a/2)=1:=by
    simpa only [mul_comm] using exp_negative_half_log_mul_sqrt ha
  have hIscale:Real.sqrt a*‖W.I‖≤CI:=by
    exact (mul_le_mul_of_nonneg_left hI (Real.sqrt_nonneg _)).trans_eq (by rw [←mul_assoc,mul_comm (Real.sqrt a) CI,mul_assoc,hScale,mul_one])
  apply (nativeRemoteReturnResponseCLM W).opNorm_le_bound (by positivity)
  intro R₀
  have hY:‖Y R₀‖≤(4*‖W.I‖)*‖R₀‖:=Y.le_of_opNorm_le hYnorm R₀
  have hQ:‖W.Q (Y R₀).val‖≤(4*CM*CI)*‖R₀‖:=by
    apply ((W.Q.le_of_opNorm_le W.native_field_bound _).trans
      (mul_le_mul_of_nonneg_left hY (by positivity))).trans
    have hh:=mul_le_mul_of_nonneg_right hIscale (by positivity:0≤4*CM*‖R₀‖)
    nlinarith only [hh]
  have hR:‖W.R (Y R₀)‖≤(4*CR*CI)*‖R₀‖:=by
    apply ((W.R.le_of_opNorm_le W.return_bound _).trans
      (mul_le_mul_of_nonneg_left hY (by positivity))).trans
    have hh:=mul_le_mul_of_nonneg_right hIscale (by positivity:0≤4*CR*‖R₀‖)
    nlinarith only [hh]
  have hRt:‖Rt R₀‖≤(1+4*CR*CI)*‖R₀‖:=by
    change ‖R₀+W.R (Y R₀)‖≤_
    exact (norm_add_le _ _).trans ((add_le_add le_rfl hR).trans_eq (by ring))
  change ‖W.Q (Y R₀).val+energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ)
    W.core W.core.smooth (Rt R₀).val-(Rt R₀).val‖≤_
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  exact (add_le_add (add_le_add hQ ((hcore _).trans (mul_le_mul_of_nonneg_left hRt hCore))) hRt).trans_eq (by ring)

#print axioms nativeRemoteReturnResponse_fixed
#print axioms nativeRemoteReturnResponse_uniform_bound
end Yamabe3.Analysis.SpherePolar
