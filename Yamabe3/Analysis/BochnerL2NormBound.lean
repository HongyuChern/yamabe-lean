import Yamabe3.Analysis.BochnerKernelSchur

/-! The Schur square estimate yields the actual L2 seminorm bound,
with exactly the same row and column constant. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal
namespace Yamabe3.Analysis

theorem eLpNorm_two_sq_eq_lintegral_enorm_sq
    {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
    (μ : Measure X) (f : X → H) :
    eLpNorm f 2 μ^2=(∫⁻ x,‖f x‖ₑ^2 ∂μ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞)≠0) (by simp)]
  simp only [ENNReal.toReal_ofNat,ENNReal.rpow_two,← ENNReal.rpow_mul_natCast,
    Nat.cast_ofNat,one_div_mul_cancel (by norm_num : (2:ℝ)≠0),ENNReal.rpow_one]

theorem bochner_kernel_eLpNorm_le
    {X Y H : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {K : X → Y → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {C : ℝ≥0∞} (hrow : ∀ x,(∫⁻ y,K x y ∂ν) ≤ C)
    (hcol : ∀ y,(∫⁻ x,K x y ∂μ) ≤ C)
    {F : Y → H} (hF : StronglyMeasurable F) (T : X → Y → H)
    (hdom : ∀ x y,‖T x y‖ₑ ≤ K x y*‖F y‖ₑ) :
    eLpNorm (fun x => ∫ y,T x y ∂ν) 2 μ ≤ C*eLpNorm F 2 ν := by
  have hs : (eLpNorm (fun x => ∫ y,T x y ∂ν) 2 μ)^2 ≤ (C*eLpNorm F 2 ν)^2 := by
    rw [eLpNorm_two_sq_eq_lintegral_enorm_sq,mul_pow,eLpNorm_two_sq_eq_lintegral_enorm_sq]
    simpa only [pow_two] using bochner_kernel_schur_square μ ν hK hrow hcol hF.enorm T hdom
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0:ℝ)<2)).mp
  simpa only [ENNReal.rpow_two] using hs

#print axioms eLpNorm_two_sq_eq_lintegral_enorm_sq
#print axioms bochner_kernel_eLpNorm_le
end Yamabe3.Analysis
