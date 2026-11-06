import Yamabe3.Analysis.LowL2Continuous
import Yamabe3.Analysis.L2TimeTranslation

/-! The low inverse is covariant under translation of the same source
and operator. This identifies all collar solutions with one global field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem futureL2Convolution_translate (k a : ℝ) (F : ℝ → H) (t : ℝ) :
    futureL2Convolution k (fun s => F (s+a)) t=futureL2Convolution k F (t+a) := by
  have h := integral_add_right_eq_self (μ := volume)
    (fun s : ℝ => futureL2Kernel k (t+a-s) • F s) a
  simpa only [futureL2Convolution,add_sub_add_right_eq_sub] using h

theorem futureL2Resolvent_translate {k : ℝ} (hk : 0 < k) (a : ℝ) (F : Lp H 2 (volume : Measure ℝ)) :
    l2TimeTranslateCLM H a (futureL2ResolventCLM k hk F)=
      futureL2ResolventCLM k hk (l2TimeTranslateCLM H a F) := by
  apply Lp.ext
  have hR := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae (futureL2Resolvent_coe_ae hk F)
  have hT := futureL2Resolvent_coe_ae hk (l2TimeTranslateCLM H a F)
  rw [futureL2Convolution_congr_ae k (l2TimeTranslate_ae H a F)] at hT
  filter_upwards [l2TimeTranslate_ae H a (futureL2ResolventCLM k hk F),hR,hT] with t ht hr hu
  change (l2TimeTranslateCLM H a (futureL2ResolventCLM k hk F) : ℝ → H) t=_
  rw [ht]
  change (futureL2ResolventCLM k hk F : ℝ → H) (t+a)=futureL2Convolution k F (t+a) at hr
  change (futureL2ResolventCLM k hk (l2TimeTranslateCLM H a F) : ℝ → H) t=
    futureL2Convolution k (fun s => F (s+a)) t at hu
  rw [hr,hu,futureL2Convolution_translate]

theorem doubleFutureL2_translate {k : ℝ} (hk : 0 < k) (a : ℝ) (F : Lp H 2 (volume : Measure ℝ)) :
    l2TimeTranslateCLM H a (doubleFutureL2CLM k hk F)=
      doubleFutureL2CLM k hk (l2TimeTranslateCLM H a F) := by
  change l2TimeTranslateCLM H a (futureL2ResolventCLM k hk (futureL2ResolventCLM k hk F))=_
  rw [futureL2Resolvent_translate,futureL2Resolvent_translate]
  rfl

theorem l2BoundedOperatorAction_translate (a : ℝ) (A : ℝ →ᵇ (H →L[ℝ] H)) (F : Lp H 2 (volume : Measure ℝ)) :
    l2TimeTranslateCLM H a (l2BoundedOperatorActionCLM A F)=
      l2BoundedOperatorActionCLM (boundedTimeTranslate (H →L[ℝ] H) a A) (l2TimeTranslateCLM H a F) := by
  apply Lp.ext
  have hm := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae (l2BoundedOperatorAction_ae A F)
  filter_upwards [l2TimeTranslate_ae H a (l2BoundedOperatorActionCLM A F),hm,
    l2BoundedOperatorAction_ae (boundedTimeTranslate (H →L[ℝ] H) a A) (l2TimeTranslateCLM H a F),
    l2TimeTranslate_ae H a F] with t ht hm hu hf
  change (l2TimeTranslateCLM H a (l2BoundedOperatorActionCLM A F) : ℝ → H) t=_
  rw [ht]
  change (l2BoundedOperatorActionCLM A F : ℝ → H) (t+a)=A (t+a) (F (t+a)) at hm
  change (l2BoundedOperatorActionCLM (boundedTimeTranslate (H →L[ℝ] H) a A) (l2TimeTranslateCLM H a F) : ℝ → H) t=
    A (t+a) ((l2TimeTranslateCLM H a F : ℝ → H) t) at hu
  rw [hm,hu,hf]

theorem lowL2FutureInverse_translate (a : ℝ) (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ ≤ 7/2)
    (F : Lp H 2 (volume : Measure ℝ)) :
    lowL2FutureInverseCLM (boundedTimeTranslate (H →L[ℝ] H) a A)
      (by rw [boundedTimeTranslate_norm];exact hA) (l2TimeTranslateCLM H a F)=
      l2TimeTranslateCLM H a (lowL2FutureInverseCLM A hA F) := by
  apply lowL2FutureInverse_unique
  rw [←l2BoundedOperatorAction_translate,←map_add,←doubleFutureL2_translate,lowL2FutureInverse_fixed]

theorem lowL2Continuous_translate (a : ℝ) (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ ≤ 7/2)
    (F : Lp H 2 (volume : Measure ℝ)) :
    lowL2ContinuousCLM (boundedTimeTranslate (H →L[ℝ] H) a A)
      (by rw [boundedTimeTranslate_norm];exact hA) (l2TimeTranslateCLM H a F)=
      boundedTimeTranslate H a (lowL2ContinuousCLM A hA F) := by
  have hS := lowL2Continuous_ae (boundedTimeTranslate (H →L[ℝ] H) a A)
    (by rw [boundedTimeTranslate_norm];exact hA) (l2TimeTranslateCLM H a F)
  rw [lowL2FutureInverse_translate a A hA F] at hS
  have hT := l2TimeTranslate_ae H a (lowL2FutureInverseCLM A hA F)
  have hC := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq (lowL2Continuous_ae A hA F)
  have hp := Measure.eq_of_ae_eq (hS.trans (hT.trans hC.symm))
    (lowL2ContinuousCLM (boundedTimeTranslate (H →L[ℝ] H) a A)
      (by rw [boundedTimeTranslate_norm];exact hA) (l2TimeTranslateCLM H a F)).continuous
    ((lowL2ContinuousCLM A hA F).continuous.comp (continuous_id.add continuous_const))
  exact BoundedContinuousFunction.ext (congrFun hp)

#print axioms futureL2Convolution_translate
#print axioms futureL2Resolvent_translate
#print axioms doubleFutureL2_translate
#print axioms l2BoundedOperatorAction_translate
#print axioms lowL2FutureInverse_translate
#print axioms lowL2Continuous_translate
end Yamabe3.Analysis.Delaunay
