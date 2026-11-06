import Yamabe3.Analysis.PositiveKernelComposition

/-! Actual repeated kernels, with transpose identities and row bounds.
The intermediate measure may be the potential-weighted measure while the
source/target measure remains the original volume. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
namespace Yamabe3.Analysis

def positiveKernelPower {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (K : X → X → ℝ≥0∞) : ℕ → X → X → ℝ≥0∞
  | 0 => K
  | n+1 => positiveKernelComp ν K (positiveKernelPower ν K n)

theorem positiveKernelPower_measurable {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {K : X → X → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (n : ℕ) :
    Measurable (Function.uncurry (positiveKernelPower ν K n)) := by
  induction n with
  | zero => exact hK
  | succ n ih => exact positiveKernelComp_measurable ν hK ih

theorem positiveKernelPower_right {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {K : X → X → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (n : ℕ) :
    positiveKernelPower ν K (n+1)=positiveKernelComp ν (positiveKernelPower ν K n) K := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change positiveKernelComp ν K (positiveKernelPower ν K (n+1))=_
    calc
      _ = positiveKernelComp ν K (positiveKernelComp ν (positiveKernelPower ν K n) K) :=
        congrArg (positiveKernelComp ν K) ih
      _ = positiveKernelComp ν (positiveKernelComp ν K (positiveKernelPower ν K n)) K :=
        (positiveKernelComp_assoc ν hK (positiveKernelPower_measurable ν hK n) hK).symm
      _ = _ := rfl

theorem positiveKernelPower_flip {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {K : X → X → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (n : ℕ) :
    Function.swap (positiveKernelPower ν K n)=positiveKernelPower ν (Function.swap K) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Function.swap (positiveKernelComp ν K (positiveKernelPower ν K n))=_
    rw [positiveKernelComp_flip,ih]
    have hf : Measurable (Function.uncurry (Function.swap K)) := hK.comp measurable_swap
    exact (positiveKernelPower_right ν hf n).symm

theorem positiveKernelPower_row_bound {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [SFinite μ] [SFinite ν] {K : X → X → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) {κ C : ℝ≥0∞}
    (hbase : ∀ x,(∫⁻ y,K x y ∂μ) ≤ C)
    (hstep : ∀ x,(∫⁻ y,K x y ∂ν) ≤ κ) (n : ℕ) :
    ∀ x,(∫⁻ y,positiveKernelPower ν K n x y ∂μ) ≤ κ^n*C := by
  induction n with
  | zero => simpa only [positiveKernelPower,pow_zero,one_mul] using hbase
  | succ n ih =>
    intro x
    have hKn := positiveKernelPower_measurable ν hK n
    have hKx : Measurable (K x) := hK.comp (measurable_const.prodMk measurable_id)
    have hm : Measurable (fun p : X × X => K x p.2*positiveKernelPower ν K n p.2 p.1) :=
      (hKx.comp measurable_snd).mul (hKn.comp measurable_swap)
    change (∫⁻ y,∫⁻ z,K x z*positiveKernelPower ν K n z y ∂ν ∂μ) ≤ _
    rw [lintegral_lintegral_swap hm.aemeasurable]
    calc
      _ = ∫⁻ z,K x z*(∫⁻ y,positiveKernelPower ν K n z y ∂μ) ∂ν := by
        apply lintegral_congr
        intro z
        exact lintegral_const_mul _ (hKn.comp (measurable_const.prodMk measurable_id))
      _ ≤ ∫⁻ z,K x z*(κ^n*C) ∂ν := by gcongr with z; exact ih z
      _ = (∫⁻ z,K x z ∂ν)*(κ^n*C) := lintegral_mul_const _ hKx
      _ ≤ κ*(κ^n*C) := by gcongr; exact hstep x
      _ = κ^(n+1)*C := by rw [pow_succ]; ac_rfl

#print axioms positiveKernelPower_right
#print axioms positiveKernelPower_flip
#print axioms positiveKernelPower_row_bound
end Yamabe3.Analysis
