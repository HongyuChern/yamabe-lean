import Mathlib.MeasureTheory.Function.L2Space

/-! The real integral pairing has its actual L2 norm bound, with no
finite-measure assumption. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis

theorem integral_mul_le_eLpNorm_two {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x,f x*g x ∂μ) ≤ (eLpNorm f 2 μ).toReal*(eLpNorm g 2 μ).toReal := by
  have he : (∫ x,f x*g x ∂μ)=inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    simp only [hx,hy,real_inner_comm,real_inner_self_eq_norm_sq,Real.inner_apply,mul_comm]
  rw [he,←Lp.norm_toLp f hf,←Lp.norm_toLp g hg]
  exact real_inner_le_norm _ _

#print axioms integral_mul_le_eLpNorm_two
end Yamabe3.Analysis
