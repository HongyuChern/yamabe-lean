import Yamabe3.Analysis.PositiveKernelPowers

/-! Composition of actual positive-kernel actions, with distinct source
and intermediate measures. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
namespace Yamabe3.Analysis

def positiveKernelAction {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (K : X → X → ℝ≥0∞) (f : X → ℝ≥0∞) (x : X) : ℝ≥0∞ := ∫⁻ y,K x y*f y ∂μ

theorem positiveKernelAction_measurable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {K : X → X → ℝ≥0∞} {f : X → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (hf : Measurable f) :
    Measurable (positiveKernelAction μ K f) :=
  (hK.mul (hf.comp measurable_snd)).lintegral_prod_right

theorem positiveKernelAction_comp {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [SFinite μ] [SFinite ν] {K L : X → X → ℝ≥0∞} {f : X → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L))
    (hf : Measurable f) :
    positiveKernelAction ν K (positiveKernelAction μ L f)=
      positiveKernelAction μ (positiveKernelComp ν K L) f := by
  funext x
  have hKx : Measurable (K x) := hK.comp (measurable_const.prodMk measurable_id)
  have hm : Measurable (fun p : X × X => K x p.1*(L p.1 p.2*f p.2)) :=
    (hKx.comp measurable_fst).mul (hL.mul (hf.comp measurable_snd))
  unfold positiveKernelAction positiveKernelComp
  calc
    _ = ∫⁻ z,∫⁻ y,K x z*(L z y*f y) ∂μ ∂ν := by
      apply lintegral_congr
      intro z
      exact (lintegral_const_mul _ ((hL.comp (measurable_const.prodMk measurable_id)).mul hf)).symm
    _ = ∫⁻ y,∫⁻ z,K x z*(L z y*f y) ∂ν ∂μ := lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro y
      simp_rw [← mul_assoc]
      exact lintegral_mul_const _ (hKx.mul (hL.comp (measurable_id.prodMk measurable_const)))

#print axioms positiveKernelAction_measurable
#print axioms positiveKernelAction_comp
end Yamabe3.Analysis
