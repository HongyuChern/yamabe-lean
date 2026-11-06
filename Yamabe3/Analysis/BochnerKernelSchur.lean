import Yamabe3.Analysis.PositiveKernelSchur
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Positive kernel domination gives both actual almost-everywhere
Bochner integrability and a genuine L2 output. Integrability is checked
separately: the convention assigning zero to undefined integrals is not
used to manufacture a source solver. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal
namespace Yamabe3.Analysis

theorem bochner_kernel_schur_square
    {X Y H : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {K : X → Y → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {A B : ℝ≥0∞} (hrow : ∀ x,(∫⁻ y,K x y ∂ν) ≤ A)
    (hcol : ∀ y,(∫⁻ x,K x y ∂μ) ≤ B)
    {f : Y → ℝ≥0∞} (hf : Measurable f) (T : X → Y → H)
    (hdom : ∀ x y,‖T x y‖ₑ ≤ K x y*f y) :
    (∫⁻ x,‖∫ y,T x y ∂ν‖ₑ^2 ∂μ) ≤ A*B*(∫⁻ y,f y^2 ∂ν) := by
  have hb (x : X) : ‖∫ y,T x y ∂ν‖ₑ ≤ ∫⁻ y,K x y*f y ∂ν :=
    (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono (hdom x))
  exact (lintegral_mono (fun x => pow_le_pow_left' (hb x) 2)).trans
    (positive_kernel_schur_square μ ν hK hrow hcol hf)

theorem bochner_kernel_schur_integrable_memLp
    {X Y H : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {K : X → Y → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {A B : ℝ≥0∞} (hA : A<⊤) (hB : B<⊤)
    (hrow : ∀ x,(∫⁻ y,K x y ∂ν) ≤ A)
    (hcol : ∀ y,(∫⁻ x,K x y ∂μ) ≤ B)
    {f : Y → ℝ≥0∞} (hf : Measurable f) (hfi : (∫⁻ y,f y^2 ∂ν)<⊤)
    (T : X → Y → H) (hT : StronglyMeasurable (Function.uncurry T))
    (hdom : ∀ x y,‖T x y‖ₑ ≤ K x y*f y) :
    (∀ᵐ x ∂μ,Integrable (T x) ν) ∧ MemLp (fun x => ∫ y,T x y ∂ν) 2 μ := by
  have hbound : A*B*(∫⁻ y,f y^2 ∂ν)<⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hA hB) hfi
  have hm : Measurable (fun x => ∫⁻ y,K x y*f y ∂ν) :=
    (hK.mul (hf.comp measurable_snd)).lintegral_prod_right
  have hi : (∫⁻ x,(∫⁻ y,K x y*f y ∂ν)^2 ∂μ)<⊤ :=
    (positive_kernel_schur_square μ ν hK hrow hcol hf).trans_lt hbound
  constructor
  · filter_upwards [ae_lt_top (hm.pow_const 2) hi.ne] with x hx
    have hx' : (∫⁻ y,K x y*f y ∂ν)<⊤ := by simpa only [ENNReal.pow_lt_top_iff,OfNat.ofNat_ne_zero,or_false] using hx
    refine ⟨(hT.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable,?_⟩
    apply hasFiniteIntegral_iff_enorm.mpr
    exact (lintegral_mono (hdom x)).trans_lt hx'
  · refine ⟨hT.integral_prod_right.aestronglyMeasurable,?_⟩
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num : (2:ℝ≥0∞)≠0) (by simp)).mpr
    have hs := (bochner_kernel_schur_square μ ν hK hrow hcol hf T hdom).trans_lt hbound
    simpa only [ENNReal.toReal_ofNat,ENNReal.rpow_two] using hs

#print axioms bochner_kernel_schur_square
#print axioms bochner_kernel_schur_integrable_memLp
end Yamabe3.Analysis
