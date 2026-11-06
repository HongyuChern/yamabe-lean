import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! Actual multiplication on real L2 by a measurable essentially
bounded coefficient, with its original coefficient and norm bound. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  (q : X → ℝ) (hq : AEStronglyMeasurable q μ) (C : ℝ) (hC : 0≤C)
  (hb : ∀ᵐ x ∂μ,‖q x‖≤C)

include hq C hC hb in
theorem l2ScalarMul_memLp (F : Lp ℝ 2 μ) : MemLp (fun x => q x*F x) 2 μ := by
  apply ((Lp.memLp F).const_mul C).mono (hq.mul (Lp.memLp F).1)
  filter_upwards [hb] with x hx
  change ‖q x*F x‖≤‖C*F x‖
  rw [norm_mul,norm_mul,Real.norm_of_nonneg hC]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

def l2ScalarMul (F : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (l2ScalarMul_memLp q hq C hC hb F).toLp (fun x => q x*F x)

theorem l2ScalarMul_ae (F : Lp ℝ 2 μ) :
    (l2ScalarMul q hq C hC hb F : X → ℝ)=ᵐ[μ] (fun x => q x*F x) :=
  (l2ScalarMul_memLp q hq C hC hb F).coeFn_toLp

theorem l2ScalarMul_norm_le (F : Lp ℝ 2 μ) : ‖l2ScalarMul q hq C hC hb F‖≤C*‖F‖ := by
  have he : eLpNorm (fun x => q x*F x) 2 μ≤eLpNorm (C • (F : X → ℝ)) 2 μ := by
    apply eLpNorm_mono_ae
    filter_upwards [hb] with x hx
    change ‖q x*F x‖≤‖C*F x‖
    rw [norm_mul,norm_mul,Real.norm_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  rw [eLpNorm_const_smul] at he
  have ht : ‖C‖ₑ*eLpNorm (F : X → ℝ) 2 μ≠⊤ := ENNReal.mul_ne_top (by simp) (Lp.memLp F).2.ne
  have hr := ENNReal.toReal_mono ht he
  unfold l2ScalarMul
  rw [Lp.norm_toLp]
  simpa only [ENNReal.toReal_mul,toReal_enorm,Lp.norm_def,Real.norm_of_nonneg hC] using hr

def l2ScalarMulCLM : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ({toFun := l2ScalarMul q hq C hC hb
    map_add' := by
      intro F G
      apply Lp.ext
      filter_upwards [l2ScalarMul_ae q hq C hC hb (F+G),l2ScalarMul_ae q hq C hC hb F,
        l2ScalarMul_ae q hq C hC hb G,Lp.coeFn_add F G,
        Lp.coeFn_add (l2ScalarMul q hq C hC hb F) (l2ScalarMul q hq C hC hb G)] with x hs hf hg hfg ho
      simpa only [Pi.add_apply,hs,hf,hg,hfg,ho] using mul_add (q x) (F x) (G x)
    map_smul' := by
      intro c F
      change l2ScalarMul q hq C hC hb (c•F)=c•l2ScalarMul q hq C hC hb F
      apply Lp.ext
      filter_upwards [l2ScalarMul_ae q hq C hC hb (c•F),l2ScalarMul_ae q hq C hC hb F,
        Lp.coeFn_smul c F,Lp.coeFn_smul c (l2ScalarMul q hq C hC hb F)] with x hs hf hcf ho
      simpa only [Pi.smul_apply,smul_eq_mul,hs,hf,hcf,ho] using mul_left_comm (q x) c (F x)
    } : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ).mkContinuous C (l2ScalarMul_norm_le q hq C hC hb)

#print axioms l2ScalarMul_memLp
#print axioms l2ScalarMul_ae
#print axioms l2ScalarMul_norm_le
#print axioms l2ScalarMulCLM
end Yamabe3.Analysis
