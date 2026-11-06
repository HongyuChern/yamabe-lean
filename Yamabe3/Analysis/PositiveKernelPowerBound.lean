import Yamabe3.Analysis.PositiveKernelPowers

/-! The same geometric row and column decay controls each actual
Neumann kernel on L2, before summing the series. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
namespace Yamabe3.Analysis

theorem positiveKernelPower_schur_square {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [SFinite μ] [SFinite ν] {K : X → X → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) {κ C : ℝ≥0∞}
    (hrow : ∀ x,(∫⁻ y,K x y ∂μ) ≤ C)
    (hcol : ∀ y,(∫⁻ x,K x y ∂μ) ≤ C)
    (hstep : ∀ x,(∫⁻ y,K x y ∂ν) ≤ κ)
    (hback : ∀ y,(∫⁻ x,K x y ∂ν) ≤ κ)
    {f : X → ℝ≥0∞} (hf : Measurable f) (n : ℕ) :
    (∫⁻ x,(∫⁻ y,positiveKernelPower ν K n x y*f y ∂μ)^2 ∂μ) ≤
      (κ^n*C)^2*(∫⁻ y,f y^2 ∂μ) := by
  have hb (y : X) : (∫⁻ x,positiveKernelPower ν K n x y ∂μ) ≤ κ^n*C := by
    have hh : Measurable (Function.uncurry (Function.swap K)) := hK.comp measurable_swap
    have he (x : X) : positiveKernelPower ν K n x y=positiveKernelPower ν (Function.swap K) n y x :=
      congrFun (congrFun (positiveKernelPower_flip ν hK n) y) x
    simp_rw [he]
    exact positiveKernelPower_row_bound μ ν hh hcol hback n y
  simpa only [pow_two] using positive_kernel_schur_square μ μ
    (positiveKernelPower_measurable ν hK n)
    (positiveKernelPower_row_bound μ ν hK hrow hstep n) hb hf

#print axioms positiveKernelPower_schur_square
end Yamabe3.Analysis
