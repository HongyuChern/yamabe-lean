import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

/-! The n = 3 normalization, with the actual signs and constants.
These identities do not supply a geometric operator or an existence theorem. -/

namespace Yamabe3

set_option autoImplicit false

theorem normalized_equation_iff (lap R u : ℝ) :
    -lap + (1 / 8 : ℝ) * R * u = (3 / 4 : ℝ) * u ^ 5 ↔
      -8 * lap + R * u = 6 * u ^ 5 := by
  constructor <;> intro h <;> linarith

/-- Algebraic last step after the geometric conformal-change formula has
been established. The nonzero hypothesis follows from strict positivity. -/
theorem curvature_six_iff (lap R u : ℝ) (hu : u ≠ 0) :
    (u ^ 5)⁻¹ * (-8 * lap + R * u) = 6 ↔
      -8 * lap + R * u = 6 * u ^ 5 := by
  rw [inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 5 hu)]
  constructor <;> intro h <;> nlinarith only [h]

end Yamabe3
