import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! The actual norm-nonincreasing linear map from L2(mu) to L2(nu)
when nu <= mu. This retains the same representative, modulo the smaller
measure, and is used for positive-time collar restriction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis
variable {X : Type*} [MeasurableSpace X] {μ ν : Measure X} (hν : ν≤μ)

def l2MeasureRestrict (F : Lp ℝ 2 μ) : Lp ℝ 2 ν :=
  ((Lp.memLp F).mono_measure hν).toLp (F : X → ℝ)

theorem l2MeasureRestrict_ae (F : Lp ℝ 2 μ) :
    (l2MeasureRestrict hν F : X → ℝ)=ᵐ[ν] (F : X → ℝ) := ((Lp.memLp F).mono_measure hν).coeFn_toLp

theorem l2MeasureRestrict_norm_le (F : Lp ℝ 2 μ) : ‖l2MeasureRestrict hν F‖≤‖F‖ := by
  have h := ENNReal.toReal_mono (Lp.memLp F).2.ne (eLpNorm_mono_measure (f := (F : X → ℝ)) (p := 2) hν)
  unfold l2MeasureRestrict
  rw [Lp.norm_toLp]
  exact h

def l2MeasureRestrictCLM : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν :=
  ({toFun := l2MeasureRestrict hν
    map_add' := by
      intro F G
      apply Lp.ext
      filter_upwards [l2MeasureRestrict_ae hν (F+G),l2MeasureRestrict_ae hν F,l2MeasureRestrict_ae hν G,
        ae_mono hν (Lp.coeFn_add F G),Lp.coeFn_add (l2MeasureRestrict hν F) (l2MeasureRestrict hν G)] with x hs hf hg hi ho
      rw [hs,ho]
      simpa only [Pi.add_apply,hf,hg] using hi
    map_smul' := by
      intro c F
      change l2MeasureRestrict hν (c•F)=c•l2MeasureRestrict hν F
      apply Lp.ext
      filter_upwards [l2MeasureRestrict_ae hν (c•F),l2MeasureRestrict_ae hν F,
        ae_mono hν (Lp.coeFn_smul c F),Lp.coeFn_smul c (l2MeasureRestrict hν F)] with x hs hf hi ho
      rw [hs,ho]
      simpa only [Pi.smul_apply,smul_eq_mul,hf] using hi
    } : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 ν).mkContinuous 1
      (by intro F;change ‖l2MeasureRestrict hν F‖≤1*‖F‖;simpa only [one_mul] using l2MeasureRestrict_norm_le hν F)

#print axioms l2MeasureRestrict_ae
#print axioms l2MeasureRestrict_norm_le
#print axioms l2MeasureRestrictCLM
end Yamabe3.Analysis
