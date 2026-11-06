import Yamabe3.Analysis.PositiveKernelSchur

/-! Associativity and measurability of actual positive-kernel integrals.
These support repeated potential kernels without interchanging conditionally
convergent Bochner integrals. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
namespace Yamabe3.Analysis

def positiveKernelComp {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (K L : X → X → ℝ≥0∞) (x y : X) : ℝ≥0∞ := ∫⁻ z,K x z*L z y ∂μ

theorem positiveKernelComp_measurable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {K L : X → X → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L)) :
    Measurable (Function.uncurry (positiveKernelComp μ K L)) := by
  have h : Measurable (fun p : (X × X) × X => K p.1.1 p.2*L p.2 p.1.2) :=
    (hK.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (hL.comp (measurable_snd.prodMk measurable_fst.snd))
  exact h.lintegral_prod_right

theorem positiveKernelComp_assoc {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {K L N : X → X → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L))
    (hN : Measurable (Function.uncurry N)) :
    positiveKernelComp μ (positiveKernelComp μ K L) N =
      positiveKernelComp μ K (positiveKernelComp μ L N) := by
  funext x y
  have hKx : Measurable (K x) := hK.comp (measurable_const.prodMk measurable_id)
  have hNy : Measurable (fun z => N z y) := hN.comp (measurable_id.prodMk measurable_const)
  have hprod : Measurable (fun p : X × X => K x p.2*L p.2 p.1*N p.1 y) :=
    ((hKx.comp measurable_snd).mul (hL.comp measurable_swap)).mul (hNy.comp measurable_fst)
  change (∫⁻ z,(∫⁻ w,K x w*L w z ∂μ)*N z y ∂μ)=∫⁻ w,K x w*(∫⁻ z,L w z*N z y ∂μ) ∂μ
  calc
    _ = ∫⁻ z,∫⁻ w,K x w*L w z*N z y ∂μ ∂μ := by
      apply lintegral_congr
      intro z
      exact (lintegral_mul_const _ (hKx.mul (hL.comp (measurable_id.prodMk measurable_const)))).symm
    _ = ∫⁻ w,∫⁻ z,K x w*L w z*N z y ∂μ ∂μ := lintegral_lintegral_swap hprod.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro w
      simp_rw [mul_assoc]
      exact lintegral_const_mul _ ((hL.comp (measurable_const.prodMk measurable_id)).mul hNy)

theorem positiveKernelComp_flip {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (K L : X → X → ℝ≥0∞) :
    Function.swap (positiveKernelComp μ K L)=
      positiveKernelComp μ (Function.swap L) (Function.swap K) := by
  funext x y
  unfold positiveKernelComp Function.swap
  apply lintegral_congr
  intro z
  exact mul_comm _ _

#print axioms positiveKernelComp_measurable
#print axioms positiveKernelComp_assoc
#print axioms positiveKernelComp_flip
end Yamabe3.Analysis
