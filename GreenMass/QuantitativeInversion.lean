import GreenMass.InversionDifferential
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Quantitative derivatives of the actual inversion map

All derivatives below are Mathlib Fréchet derivatives of the actual inversion
map on a real inner-product space. No auxiliary array is called a derivative.
-/
set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
namespace GreenMass.QuantitativeInversion
open InversionDifferential
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact reciprocal-radius identity for the genuine inversion. -/
theorem norm_inversion (x : E) (hx : x ≠ 0) :
    ‖inversion x‖ = ‖x‖⁻¹ := by
  have hn := norm_ne_zero_iff.mpr hx
  rw [inversion, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (‖x‖^2)⁻¹)]
  field_simp [hn]

/-- A dimension-independent operator-norm bound for the true first differential. -/
theorem norm_fderiv_inversion_le (x : E) (hx : x ≠ 0) :
    ‖fderiv ℝ inversion x‖ ≤ 3 * (‖x‖^2)⁻¹ := by
  rw [fderiv_inversion x hx]
  have hn := norm_ne_zero_iff.mpr hx
  calc
    ‖inversionDerivative x‖ ≤
      ‖(‖x‖^2)⁻¹ • ContinuousLinearMap.id ℝ E‖ +
        ‖(2 * (‖x‖^4)⁻¹) • (innerSL ℝ x).smulRight x‖ := norm_sub_le _ _
    _ = (‖x‖^2)⁻¹ * ‖ContinuousLinearMap.id ℝ E‖ +
        (2 * (‖x‖^4)⁻¹) * ‖(innerSL ℝ x).smulRight x‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (‖x‖^2)⁻¹),
        Real.norm_of_nonneg (by positivity : 0 ≤ 2 * (‖x‖^4)⁻¹)]
    _ ≤ (‖x‖^2)⁻¹ * 1 + (2 * (‖x‖^4)⁻¹) * (‖x‖ * ‖x‖) := by
      gcongr
      · exact ContinuousLinearMap.norm_id_le
      · rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
    _ = 3 * (‖x‖^2)⁻¹ := by field_simp [hn]; ring

/-- Applying the genuine derivative costs at most the same R^-2 scale. -/
theorem norm_fderiv_inversion_apply_le (x v : E) (hx : x ≠ 0) :
    ‖fderiv ℝ inversion x v‖ ≤ 3 * (‖x‖^2)⁻¹ * ‖v‖ :=
  (ContinuousLinearMap.le_opNorm _ _).trans <|
    mul_le_mul_of_nonneg_right (norm_fderiv_inversion_le x hx) (norm_nonneg _)

#print axioms norm_inversion
#print axioms norm_fderiv_inversion_le
#print axioms norm_fderiv_inversion_apply_le
end GreenMass.QuantitativeInversion

#check GreenMass.QuantitativeInversion.norm_inversion
#check GreenMass.QuantitativeInversion.norm_fderiv_inversion_le
#check GreenMass.QuantitativeInversion.norm_fderiv_inversion_apply_le
