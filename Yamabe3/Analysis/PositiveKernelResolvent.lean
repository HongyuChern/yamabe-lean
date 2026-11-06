import Yamabe3.Analysis.PositiveKernelPowers
import Mathlib.Analysis.SpecificLimits.Basic

/-! The positive Neumann majorant is an actual measurable kernel. Its
row/column bounds and L2 square estimate follow from two weighted kernel
gaps. This is an estimate, not yet an elliptic source solver. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
namespace Yamabe3.Analysis

def positiveKernelResolvent {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (K : X → X → ℝ≥0∞) (x y : X) : ℝ≥0∞ := ∑' n,positiveKernelPower ν K n x y

theorem positiveKernelResolvent_measurable {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {K : X → X → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) :
    Measurable (Function.uncurry (positiveKernelResolvent ν K)) :=
  Measurable.ennreal_tsum (fun n => positiveKernelPower_measurable ν hK n)

theorem positiveKernelResolvent_row_bound {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [SFinite μ] [SFinite ν] {K : X → X → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) {κ C : ℝ≥0∞}
    (hbase : ∀ x,(∫⁻ y,K x y ∂μ) ≤ C)
    (hstep : ∀ x,(∫⁻ y,K x y ∂ν) ≤ κ) (x : X) :
    (∫⁻ y,positiveKernelResolvent ν K x y ∂μ) ≤ (1-κ)⁻¹*C := by
  unfold positiveKernelResolvent
  have hm (n : ℕ) : Measurable (fun y => positiveKernelPower ν K n x y) :=
    (positiveKernelPower_measurable ν hK n).comp (measurable_const.prodMk measurable_id)
  rw [lintegral_tsum (fun n => (hm n).aemeasurable)]
  calc
    _ ≤ ∑' n,κ^n*C := ENNReal.tsum_le_tsum (fun n => positiveKernelPower_row_bound μ ν hK hbase hstep n x)
    _ = _ := by rw [ENNReal.tsum_mul_right,ENNReal.tsum_geometric]

theorem positiveKernelResolvent_flip {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {K : X → X → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) :
    Function.swap (positiveKernelResolvent ν K)=positiveKernelResolvent ν (Function.swap K) := by
  funext x y
  unfold positiveKernelResolvent Function.swap
  apply tsum_congr
  intro n
  exact congrFun (congrFun (positiveKernelPower_flip ν hK n) x) y

theorem positiveKernelResolvent_schur_bound {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [SFinite μ] [SFinite ν] {K : X → X → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) {κ C : ℝ≥0∞}
    (hrow : ∀ x,(∫⁻ y,K x y ∂μ) ≤ C)
    (hcol : ∀ y,(∫⁻ x,K x y ∂μ) ≤ C)
    (hstep : ∀ x,(∫⁻ y,K x y ∂ν) ≤ κ)
    (hback : ∀ y,(∫⁻ x,K x y ∂ν) ≤ κ)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x,(∫⁻ y,positiveKernelResolvent ν K x y*f y ∂μ)^2 ∂μ) ≤
      ((1-κ)⁻¹*C)^2*(∫⁻ y,f y^2 ∂μ) := by
  have hb : ∀ y,(∫⁻ x,positiveKernelResolvent ν K x y ∂μ) ≤ (1-κ)⁻¹*C := by
    intro y
    have hh : Measurable (Function.uncurry (Function.swap K)) := hK.comp measurable_swap
    have he (x : X) : positiveKernelResolvent ν K x y=positiveKernelResolvent ν (Function.swap K) y x :=
      congrFun (congrFun (positiveKernelResolvent_flip ν hK) y) x
    simp_rw [he]
    exact positiveKernelResolvent_row_bound μ ν hh hcol hback y
  simpa only [pow_two] using positive_kernel_schur_square μ μ
    (positiveKernelResolvent_measurable ν hK)
    (positiveKernelResolvent_row_bound μ ν hK hrow hstep) hb hf

#print axioms positiveKernelResolvent_row_bound
#print axioms positiveKernelResolvent_flip
#print axioms positiveKernelResolvent_schur_bound
end Yamabe3.Analysis
