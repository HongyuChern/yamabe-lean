import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-! The actual positive-kernel Schur square estimate. No finite input
moments, pointwise finiteness or operator norm is assumed in this
extended-nonnegative inequality. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
namespace Yamabe3.Analysis

theorem lintegral_square_le_mass_mul {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ x,f x ∂μ)^2 ≤ μ univ * (∫⁻ x,f x^2 ∂μ) := by
  have hp : Real.HolderConjugate 2 2 := by
    apply Real.holderConjugate_iff.mpr
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hp
    (f := fun _ => 1) (g := f) aemeasurable_const hf
  simp only [Pi.mul_apply,one_mul,ENNReal.rpow_two] at h
  have hh := pow_le_pow_left' h 2
  simpa only [mul_pow,← ENNReal.rpow_mul_natCast,one_pow,lintegral_one,
    Nat.cast_ofNat,one_div_mul_cancel (by norm_num : (2:ℝ) ≠ 0),ENNReal.rpow_one] using hh

theorem lintegral_weighted_square_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {K f : X → ℝ≥0∞} (hK : Measurable K) (hf : Measurable f) :
    (∫⁻ x,K x*f x ∂μ)^2 ≤ (∫⁻ x,K x ∂μ)*(∫⁻ x,K x*f x^2 ∂μ) := by
  have h := lintegral_square_le_mass_mul (μ := μ.withDensity K) hf.aemeasurable
  simpa only [lintegral_withDensity_eq_lintegral_mul μ hK hf,
    lintegral_withDensity_eq_lintegral_mul μ hK (hf.pow_const 2),
    withDensity_apply K MeasurableSet.univ,Measure.restrict_univ,Pi.mul_apply] using h

theorem positive_kernel_schur_square
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {K : X → Y → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {A B : ℝ≥0∞} (hrow : ∀ x,(∫⁻ y,K x y ∂ν) ≤ A)
    (hcol : ∀ y,(∫⁻ x,K x y ∂μ) ≤ B)
    {f : Y → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x,(∫⁻ y,K x y*f y ∂ν)^2 ∂μ) ≤ A*B*(∫⁻ y,f y^2 ∂ν) := by
  have hprod : Measurable (fun p : X × Y => K p.1 p.2*f p.2^2) :=
    hK.mul ((hf.comp measurable_snd).pow_const 2)
  calc
    _ ≤ ∫⁻ x,A*(∫⁻ y,K x y*f y^2 ∂ν) ∂μ := by
      apply lintegral_mono
      intro x
      calc
        _ ≤ (∫⁻ y,K x y ∂ν)*(∫⁻ y,K x y*f y^2 ∂ν) :=
          lintegral_weighted_square_le ν (hK.comp (measurable_const.prodMk measurable_id)) hf
        _ ≤ A*(∫⁻ y,K x y*f y^2 ∂ν) := by gcongr; exact hrow x
    _ = A*(∫⁻ x,∫⁻ y,K x y*f y^2 ∂ν ∂μ) :=
      lintegral_const_mul A hprod.lintegral_prod_right
    _ = A*(∫⁻ y,∫⁻ x,K x y*f y^2 ∂μ ∂ν) := by
      rw [lintegral_lintegral_swap hprod.aemeasurable]
    _ = A*(∫⁻ y,(∫⁻ x,K x y ∂μ)*f y^2 ∂ν) := by
      congr 1
      apply lintegral_congr
      intro y
      exact lintegral_mul_const _ (hK.comp (measurable_id.prodMk measurable_const))
    _ ≤ A*(∫⁻ y,B*f y^2 ∂ν) := by
      gcongr with y
      exact hcol y
    _ = A*B*(∫⁻ y,f y^2 ∂ν) := by
      rw [lintegral_const_mul B (hf.pow_const 2),mul_assoc]

#print axioms lintegral_weighted_square_le
#print axioms positive_kernel_schur_square
end Yamabe3.Analysis
