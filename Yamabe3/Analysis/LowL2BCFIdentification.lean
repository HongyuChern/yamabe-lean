import Yamabe3.Analysis.LowL2Continuous

/-! The L2 inverse and the earlier bounded-continuous inverse agree on
 their actual common source domain. No L2 integrability of the old
 solution is assumed: it follows from the newly constructed L2 solution. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

theorem lowL2Continuous_BCF_fixed (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ ≤ 7/2)
    (F : ℝ →ᵇ H) (hF : MemLp F 2) :
    banachDoubleFutureResolvent 2 (by norm_num)
      (F+boundedOperatorAction A (lowL2ContinuousCLM A hA (hF.toLp F))) =
      lowL2ContinuousCLM A hA (hF.toLp F) := by
  let U := lowL2ContinuousCLM A hA (hF.toLp F)
  let R := lowL2FutureInverseCLM A hA (hF.toLp F)
  let G := F+boundedOperatorAction A U
  let G₂ := lowL2EffectiveSourceCLM A hA (hF.toLp F)
  have hU : (U : ℝ → H)=ᵐ[volume](R : ℝ → H) := lowL2Continuous_ae A hA _
  have hGae : (G₂ : ℝ → H)=ᵐ[volume](G : ℝ → H) := by
    have hh := Lp.coeFn_add (hF.toLp F) (l2BoundedOperatorActionCLM A R)
    filter_upwards [hh,hF.coeFn_toLp,l2BoundedOperatorAction_ae A R,hU] with t ha hf hb hu
    change G₂ t=G t
    change (hF.toLp F+l2BoundedOperatorActionCLM A R) t=_ at ha
    change (l2BoundedOperatorActionCLM A R : ℝ → H) t=A t (R t) at hb
    change (hF.toLp F+l2BoundedOperatorActionCLM A R) t=F t+A t (U t)
    rw [ha]
    change (hF.toLp F) t+(l2BoundedOperatorActionCLM A R) t=F t+A t (U t)
    rw [hf,hb,hu]
  have hG : MemLp G 2 := (Lp.memLp G₂).ae_eq hGae
  have hGid : hG.toLp G=G₂ := Lp.ext (hG.coeFn_toLp.trans hGae.symm)
  have hdouble := doubleFutureL2_agrees_original (by norm_num : (0:ℝ)<2) G hG
  rw [hGid] at hdouble
  have hfixed : doubleFutureL2CLM 2 (by norm_num) G₂=R := lowL2FutureInverse_fixed A hA _
  rw [hfixed] at hdouble
  have he := Measure.eq_of_ae_eq (hdouble.symm.trans hU.symm)
    (banachDoubleFutureResolvent 2 (by norm_num) G).continuous U.continuous
  exact BoundedContinuousFunction.ext (congrFun he)

theorem lowL2Continuous_agrees_BCF (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ ≤ 7/2)
    (F : ℝ →ᵇ H) (hF : MemLp F 2) :
    lowL2ContinuousCLM A hA (hF.toLp F)=
      banachFuturePotentialInverse 2 (by norm_num) A (by nlinarith) F := by
  have hf : Function.IsFixedPt (banachFuturePotentialIteration 2 (by norm_num) A F)
      (lowL2ContinuousCLM A hA (hF.toLp F)) := lowL2Continuous_BCF_fixed A hA F hF
  exact (banachFuturePotentialIteration_contracting (by norm_num : (0:ℝ)<2)
    A (by nlinarith) F).fixedPoint_unique hf

theorem banachFuturePotentialInverse_memLp (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ ≤ 7/2)
    (F : ℝ →ᵇ H) (hF : MemLp F 2) :
    MemLp (banachFuturePotentialInverse 2 (by norm_num) A (by nlinarith) F) 2 := by
  rw [←lowL2Continuous_agrees_BCF A hA F hF]
  exact (Lp.memLp (lowL2FutureInverseCLM A hA (hF.toLp F))).ae_eq (lowL2Continuous_ae A hA _).symm

theorem lowL2Continuous_BCF_equation (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ ≤ 7/2)
    (F : ℝ →ᵇ H) (hF : MemLp F 2) :
    let U := lowL2ContinuousCLM A hA (hF.toLp F)
    Differentiable ℝ (fun t => U t) ∧ Differentiable ℝ (deriv (fun t => U t)) ∧
      ∀ t, deriv (deriv (fun s => U s)) t =
        (4:ℝ) • deriv (fun s => U s) t-(4:ℝ) • U t+F t+A t (U t) := by
  dsimp only
  rw [lowL2Continuous_agrees_BCF A hA F hF]
  simpa only [show (2:ℝ)*2=4 by norm_num,show (2:ℝ)^2=4 by norm_num] using
    banachFuturePotentialInverse_equation (by norm_num : (0:ℝ)<2) A (by nlinarith) F

#print axioms lowL2Continuous_BCF_fixed
#print axioms lowL2Continuous_agrees_BCF
#print axioms banachFuturePotentialInverse_memLp
#print axioms lowL2Continuous_BCF_equation
end Yamabe3.Analysis.Delaunay
