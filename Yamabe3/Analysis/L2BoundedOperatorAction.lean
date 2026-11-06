import Yamabe3.Analysis.FutureL2Resolvent
import Yamabe3.Analysis.BanachFuturePotentialInverse

/-! Actual time-dependent bounded operator multiplication on the L2
quotient, with no pointwise representative regularity assumption. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

 theorem l2BoundedOperator_memLp (A : ℝ →ᵇ (H →L[ℝ] H)) (F : Lp H 2 (volume : Measure ℝ)) :
    MemLp (fun t => A t (F t)) 2 := by
  have hAn : 0≤‖A‖ := (norm_nonneg (A 0)).trans (A.norm_coe_le_norm 0)
  apply ((Lp.memLp F).const_smul ‖A‖).mono
    ((show Continuous (fun p : (H →L[ℝ] H) × H => p.1 p.2) from
      continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (A.continuous.aestronglyMeasurable.prodMk (Lp.memLp F).1))
  exact Eventually.of_forall fun t => by
    rw [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg hAn]
    exact ((A t).le_opNorm (F t)).trans
      (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm t) (norm_nonneg _))

def l2BoundedOperatorAction (A : ℝ →ᵇ (H →L[ℝ] H)) (F : Lp H 2 (volume : Measure ℝ)) :
    Lp H 2 (volume : Measure ℝ) := (l2BoundedOperator_memLp A F).toLp (fun t => A t (F t))

theorem l2BoundedOperatorAction_ae (A : ℝ →ᵇ (H →L[ℝ] H)) (F : Lp H 2 (volume : Measure ℝ)) :
    (l2BoundedOperatorAction A F : ℝ → H)=ᵐ[volume](fun t => A t (F t)) :=
  (l2BoundedOperator_memLp A F).coeFn_toLp

theorem l2BoundedOperatorAction_norm (A : ℝ →ᵇ (H →L[ℝ] H)) (F : Lp H 2 (volume : Measure ℝ)) :
    ‖l2BoundedOperatorAction A F‖≤‖A‖*‖F‖ := by
  have hAn : 0≤‖A‖ := (norm_nonneg (A 0)).trans (A.norm_coe_le_norm 0)
  have hb : eLpNorm (fun t => A t (F t)) 2≤eLpNorm (‖A‖ • (F : ℝ → H)) 2 := by
    apply eLpNorm_mono_ae
    exact Eventually.of_forall fun t => by
      rw [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg hAn]
      exact ((A t).le_opNorm (F t)).trans
        (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm t) (norm_nonneg _))
  rw [eLpNorm_const_smul] at hb
  have ht : ‖‖A‖‖ₑ*eLpNorm (F : ℝ → H) 2≠⊤ :=
    ENNReal.mul_ne_top (by simp) (Lp.memLp F).2.ne
  have hr := ENNReal.toReal_mono ht hb
  unfold l2BoundedOperatorAction
  rw [Lp.norm_toLp]
  simpa only [ENNReal.toReal_mul,enorm_norm,toReal_enorm,Real.norm_of_nonneg hAn,Lp.norm_def] using hr

theorem l2BoundedOperatorAction_add (A : ℝ →ᵇ (H →L[ℝ] H)) (F G : Lp H 2 (volume : Measure ℝ)) :
    l2BoundedOperatorAction A (F+G)=l2BoundedOperatorAction A F+l2BoundedOperatorAction A G := by
  apply Lp.ext
  filter_upwards [l2BoundedOperatorAction_ae A (F+G),l2BoundedOperatorAction_ae A F,
    l2BoundedOperatorAction_ae A G,Lp.coeFn_add F G,
    Lp.coeFn_add (l2BoundedOperatorAction A F) (l2BoundedOperatorAction A G)] with t hs hf hg hfg ho
  simpa only [Pi.add_apply,hs,hf,hg,hfg,ho] using (A t).map_add (F t) (G t)

theorem l2BoundedOperatorAction_smul (A : ℝ →ᵇ (H →L[ℝ] H)) (c : ℝ) (F : Lp H 2 (volume : Measure ℝ)) :
    l2BoundedOperatorAction A (c • F)=c • l2BoundedOperatorAction A F := by
  apply Lp.ext
  filter_upwards [l2BoundedOperatorAction_ae A (c • F),l2BoundedOperatorAction_ae A F,
    Lp.coeFn_smul c F,Lp.coeFn_smul c (l2BoundedOperatorAction A F)] with t hs hf hcf ho
  simpa only [Pi.smul_apply,hs,hf,hcf,ho] using (A t).map_smul c (F t)

def l2BoundedOperatorActionCLM (A : ℝ →ᵇ (H →L[ℝ] H)) :
    Lp H 2 (volume : Measure ℝ) →L[ℝ] Lp H 2 (volume : Measure ℝ) :=
  ({toFun := l2BoundedOperatorAction A
    map_add' := l2BoundedOperatorAction_add A
    map_smul' := l2BoundedOperatorAction_smul A} :
      Lp H 2 (volume : Measure ℝ) →ₗ[ℝ] Lp H 2 (volume : Measure ℝ)).mkContinuous
    ‖A‖ (l2BoundedOperatorAction_norm A)

theorem l2BoundedOperatorActionCLM_norm (A : ℝ →ᵇ (H →L[ℝ] H)) :
    ‖l2BoundedOperatorActionCLM A‖≤‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg (A 0)).trans (A.norm_coe_le_norm 0)) (l2BoundedOperatorAction_norm A)

#print axioms l2BoundedOperator_memLp
#print axioms l2BoundedOperatorAction_ae
#print axioms l2BoundedOperatorAction_norm
#print axioms l2BoundedOperatorAction_add
#print axioms l2BoundedOperatorAction_smul
#print axioms l2BoundedOperatorActionCLM_norm
end Yamabe3.Analysis.Delaunay
