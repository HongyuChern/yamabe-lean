import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The actual differential of radial inversion

The inversion is an actual map of a real inner product space. Its derivative
is proved by the norm-square derivative, inverse chain rule, and scalar-vector
product rule. This closes the differential calculation separately from the
matrix algebra in `Inversion.lean`. At zero the formula is not asserted.
-/

set_option autoImplicit false
noncomputable section

open scoped RealInnerProductSpace

namespace GreenMass.InversionDifferential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Radial inversion, with the usual totalized inverse at zero. -/
def inversion (x : E) : E := (‖x‖ ^ 2)⁻¹ • x

/-- The candidate continuous linear derivative, with its explicit radial term. -/
def inversionDerivative (x : E) : E →L[ℝ] E :=
  (‖x‖ ^ 2)⁻¹ • ContinuousLinearMap.id ℝ E -
    (2 * (‖x‖ ^ 4)⁻¹) • (innerSL ℝ x).smulRight x

theorem inversionDerivative_apply (x v : E) :
    inversionDerivative x v =
      (‖x‖ ^ 2)⁻¹ • v - (2 * (‖x‖ ^ 4)⁻¹ * ⟪x, v⟫) • x := by
  simp [inversionDerivative, smul_smul]

/-- The full Frechet derivative of the genuine inversion map at a nonzero point. -/
theorem hasFDerivAt_inversion (x : E) (hx : x ≠ 0) :
    HasFDerivAt inversion (inversionDerivative x) x := by
  have hnorm : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hsquare : HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hinverse : HasFDerivAt (fun y : E => (‖y‖ ^ 2)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-((‖x‖ ^ 2) ^ 2)⁻¹)).comp
        (2 • innerSL ℝ x)) x :=
    (hasFDerivAt_inv hnorm).comp x hsquare
  have hproduct : HasFDerivAt (inversion : E → E)
      ((‖x‖ ^ 2)⁻¹ • ContinuousLinearMap.id ℝ E +
        ((ContinuousLinearMap.toSpanSingleton ℝ (-((‖x‖ ^ 2) ^ 2)⁻¹)).comp
          (2 • innerSL ℝ x)).smulRight x) x :=
    hinverse.smul (hasFDerivAt_id x)
  have hmap : inversionDerivative x =
      (‖x‖ ^ 2)⁻¹ • ContinuousLinearMap.id ℝ E +
        ((ContinuousLinearMap.toSpanSingleton ℝ (-((‖x‖ ^ 2) ^ 2)⁻¹)).comp
          (2 • innerSL ℝ x)).smulRight x := by
    ext v
    simp only [inversionDerivative, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, smul_smul]
    norm_num only [pow_mul]
    module
  rw [hmap]
  exact hproduct

theorem fderiv_inversion (x : E) (hx : x ≠ 0) :
    fderiv ℝ inversion x = inversionDerivative x :=
  (hasFDerivAt_inversion x hx).fderiv

theorem fderiv_inversion_apply (x v : E) (hx : x ≠ 0) :
    fderiv ℝ inversion x v =
      (‖x‖ ^ 2)⁻¹ • v - (2 * (‖x‖ ^ 4)⁻¹ * ⟪x, v⟫) • x := by
  rw [fderiv_inversion x hx, inversionDerivative_apply]

#print axioms inversionDerivative_apply
#print axioms hasFDerivAt_inversion
#print axioms fderiv_inversion
#print axioms fderiv_inversion_apply

end GreenMass.InversionDifferential
