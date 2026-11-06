import Yamabe3.Analysis.SmoothPeriodicClock
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The explicit three-dimensional Delaunay energy oval

The squared neck is `a`, and the squared maximum `b` is explicitly solved
from `a² + a*b + b² = 1`. The trigonometric parametrization resolves both
turning points. Its positive time density is smooth everywhere, so that the
actual inverse constructed in `SmoothPeriodicClock` yields a global orbit.
All derivative identities use the normalization `v'' = v/4 - 3*v^5/4`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

/-- The other positive root on the negative-energy oval, in squared values. -/
def upperSquared (a : ℝ) : ℝ := (Real.sqrt (4 - 3 * a ^ 2) - a) / 2

theorem upperSquared_properties {a : ℝ} (ha : 0 < a) (hsmall : 3 * a ^ 2 < 1) :
    a < upperSquared a ∧ upperSquared a < 1 ∧
      a ^ 2 + a * upperSquared a + upperSquared a ^ 2 = 1 := by
  have hr : 0 ≤ 4 - 3 * a ^ 2 := by linarith
  have hs := Real.sq_sqrt hr
  have hp := Real.sqrt_nonneg (4 - 3 * a ^ 2)
  have ha1 : a < 1 := by nlinarith
  have hlow : 3 * a < Real.sqrt (4 - 3 * a ^ 2) := by nlinarith
  have hupp : Real.sqrt (4 - 3 * a ^ 2) < 2 + a := by nlinarith
  dsimp [upperSquared]
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith

/-- Squared profile on the energy oval. -/
def ovalSquared (a b θ : ℝ) : ℝ := a + (b - a) * Real.sin θ ^ 2
/-- The positive angular profile. -/
def ovalProfile (a b θ : ℝ) : ℝ := Real.sqrt (ovalSquared a b θ)
/-- The remaining positive factor of the energy polynomial. -/
def ovalFactor (a b θ : ℝ) : ℝ := ovalSquared a b θ + a + b
/-- Angular speed in physical cylindrical time. -/
def ovalSpeed (a b θ : ℝ) : ℝ :=
  ovalProfile a b θ * Real.sqrt (ovalFactor a b θ) / 2
/-- Actual elapsed time per angular increment. -/
def ovalDensity (a b θ : ℝ) : ℝ := (ovalSpeed a b θ)⁻¹
/-- Actual derivative of the profile in physical cylindrical time. -/
def ovalVelocity (a b θ : ℝ) : ℝ :=
  (b - a) / 2 * Real.sin θ * Real.cos θ * Real.sqrt (ovalFactor a b θ)

theorem ovalSquared_bounds {a b : ℝ} (hab : a ≤ b) (θ : ℝ) :
    a ≤ ovalSquared a b θ ∧ ovalSquared a b θ ≤ b := by
  have hs := sq_nonneg (Real.sin θ)
  have hc := sq_nonneg (Real.cos θ)
  have hid := Real.sin_sq_add_cos_sq θ
  dsimp [ovalSquared]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hab) hs,
    mul_nonneg (sub_nonneg.mpr hab) hc]

theorem ovalSquared_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ : ℝ) :
    0 < ovalSquared a b θ := ha.trans_le (ovalSquared_bounds hab θ).1

theorem ovalFactor_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ : ℝ) :
    0 < ovalFactor a b θ := by
  have := ovalSquared_pos ha hab θ
  dsimp [ovalFactor]
  linarith

theorem ovalProfile_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ : ℝ) :
    0 < ovalProfile a b θ := Real.sqrt_pos.mpr (ovalSquared_pos ha hab θ)

theorem ovalProfile_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ : ℝ) :
    ovalProfile a b θ ^ 2 = ovalSquared a b θ :=
  Real.sq_sqrt (ovalSquared_pos ha hab θ).le

theorem ovalProfile_bounds {a b : ℝ} (hab : a ≤ b) (θ : ℝ) :
    Real.sqrt a ≤ ovalProfile a b θ ∧ ovalProfile a b θ ≤ Real.sqrt b :=
  ⟨Real.sqrt_le_sqrt (ovalSquared_bounds hab θ).1,
   Real.sqrt_le_sqrt (ovalSquared_bounds hab θ).2⟩

/-- Between successive turning maxima the profile is strictly below the maximum. -/
theorem ovalProfile_lt_upper {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {θ : ℝ} (hcos : Real.cos θ ≠ 0) : ovalProfile a b θ < Real.sqrt b := by
  have hcs : 0 < Real.cos θ ^ 2 := sq_pos_of_ne_zero hcos
  have htrig := Real.sin_sq_add_cos_sq θ
  have hw : ovalSquared a b θ < b := by
    dsimp [ovalSquared]
    nlinarith [mul_pos (sub_pos.mpr hab) hcs]
  exact Real.sqrt_lt_sqrt (ovalSquared_pos ha hab.le θ).le hw

theorem ovalSpeed_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ : ℝ) :
    0 < ovalSpeed a b θ :=
  div_pos (mul_pos (ovalProfile_pos ha hab θ)
    (Real.sqrt_pos.mpr (ovalFactor_pos ha hab θ))) (by norm_num)

theorem ovalSpeed_le_one {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1) (θ : ℝ) : ovalSpeed a b θ ≤ 1 := by
  have hw := ovalSquared_bounds hab θ
  have hV : ovalProfile a b θ ≤ 1 := Real.sqrt_le_one.mpr (hw.2.trans hb)
  have hK : Real.sqrt (ovalFactor a b θ) ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · dsimp [ovalFactor]; nlinarith
  have hV0 := (ovalProfile_pos ha hab θ).le
  have hK0 := Real.sqrt_nonneg (ovalFactor a b θ)
  dsimp [ovalSpeed]
  nlinarith [mul_le_mul hV hK hK0 (by norm_num : (0 : ℝ) ≤ 1)]

theorem ovalDensity_ge_one {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1) (θ : ℝ) : 1 ≤ ovalDensity a b θ := by
  have hp := ovalSpeed_pos ha hab θ
  have hbnd := ovalSpeed_le_one ha hab hb θ
  exact (one_le_inv₀ hp).mpr hbnd

theorem ovalDensity_formula {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ : ℝ) :
    ovalDensity a b θ = 2 / Real.sqrt
      (ovalSquared a b θ * (ovalSquared a b θ + a + b)) := by
  rw [Real.sqrt_mul (ovalSquared_pos ha hab θ).le]
  dsimp [ovalDensity, ovalSpeed, ovalProfile, ovalFactor]
  field_simp

theorem ovalSquared_contDiff (a b : ℝ) : ContDiff ℝ ∞ (ovalSquared a b) := by
  exact contDiff_const.add (contDiff_const.mul (Real.contDiff_sin.pow 2))

theorem ovalProfile_contDiff {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContDiff ℝ ∞ (ovalProfile a b) :=
  (ovalSquared_contDiff a b).sqrt (fun θ => (ovalSquared_pos ha hab θ).ne')

theorem ovalFactor_contDiff (a b : ℝ) : ContDiff ℝ ∞ (ovalFactor a b) :=
  ((ovalSquared_contDiff a b).add contDiff_const).add contDiff_const

theorem ovalDensity_contDiff {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContDiff ℝ ∞ (ovalDensity a b) := by
  have hs : ContDiff ℝ ∞ (ovalSpeed a b) :=
    ((ovalProfile_contDiff ha hab).mul
      ((ovalFactor_contDiff a b).sqrt (fun θ => (ovalFactor_pos ha hab θ).ne'))).div_const 2
  exact hs.inv (fun θ => (ovalSpeed_pos ha hab θ).ne')

theorem ovalProfile_periodic (a b : ℝ) :
    Function.Periodic (ovalProfile a b) Real.pi := by
  intro θ
  simp only [ovalProfile, ovalSquared, Real.sin_add_pi, neg_sq]

theorem ovalDensity_periodic (a b : ℝ) :
    Function.Periodic (ovalDensity a b) Real.pi := by
  intro θ
  simp only [ovalDensity, ovalSpeed, ovalProfile, ovalFactor, ovalSquared,
    Real.sin_add_pi, neg_sq]

theorem ovalSquared_hasDerivAt (a b θ : ℝ) :
    HasDerivAt (ovalSquared a b) (2 * (b - a) * Real.sin θ * Real.cos θ) θ := by
  change HasDerivAt (fun t => a + (b - a) * Real.sin t ^ 2) _ θ
  apply ((((Real.hasDerivAt_sin θ).pow 2).const_mul (b - a)).const_add a).congr_deriv
  norm_num
  ring

theorem ovalProfile_hasDerivAt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ : ℝ) :
    HasDerivAt (ovalProfile a b)
      ((b - a) * Real.sin θ * Real.cos θ / ovalProfile a b θ) θ := by
  unfold ovalProfile
  apply ((ovalSquared_hasDerivAt a b θ).sqrt (ovalSquared_pos ha hab θ).ne').congr_deriv
  ring

theorem ovalProfile_derivative_speed {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ : ℝ) :
    ((b - a) * Real.sin θ * Real.cos θ / ovalProfile a b θ) * ovalSpeed a b θ =
      ovalVelocity a b θ := by
  have hp := (ovalProfile_pos ha hab θ).ne'
  dsimp [ovalSpeed, ovalVelocity]
  field_simp

/-- Derivative of the angular velocity, with both turning points included. -/
theorem ovalVelocity_hasDerivAt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ : ℝ) :
    HasDerivAt (ovalVelocity a b)
      ((b - a) / 2 * (Real.cos θ ^ 2 - Real.sin θ ^ 2) *
          Real.sqrt (ovalFactor a b θ) +
        (b - a) ^ 2 / 2 * Real.sin θ ^ 2 * Real.cos θ ^ 2 /
          Real.sqrt (ovalFactor a b θ)) θ := by
  have hF := ((ovalSquared_hasDerivAt a b θ).add_const a).add_const b
  have hS := hF.sqrt (ovalFactor_pos ha hab θ).ne'
  have h := ((((Real.hasDerivAt_sin θ).const_mul ((b - a) / 2)).mul
    (Real.hasDerivAt_cos θ)).mul hS)
  unfold ovalVelocity ovalFactor
  apply h.congr_deriv
  simp only [Pi.mul_apply]
  ring

theorem ovalVelocity_derivative_speed {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlevel : a ^ 2 + a * b + b ^ 2 = 1) (θ : ℝ) :
    ((b - a) / 2 * (Real.cos θ ^ 2 - Real.sin θ ^ 2) *
          Real.sqrt (ovalFactor a b θ) +
        (b - a) ^ 2 / 2 * Real.sin θ ^ 2 * Real.cos θ ^ 2 /
          Real.sqrt (ovalFactor a b θ)) * ovalSpeed a b θ =
      ovalProfile a b θ / 4 - 3 * ovalProfile a b θ ^ 5 / 4 := by
  have hK := (Real.sqrt_pos.mpr (ovalFactor_pos ha hab θ)).ne'
  have hKs := Real.sq_sqrt (ovalFactor_pos ha hab θ).le
  have hVs := ovalProfile_sq ha hab θ
  have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  have hpoly :
      (b - a) * (Real.cos θ ^ 2 - Real.sin θ ^ 2) * ovalFactor a b θ +
        (b - a) ^ 2 * Real.sin θ ^ 2 * Real.cos θ ^ 2 =
      1 - 3 * ovalSquared a b θ ^ 2 := by
    rw [hc]
    dsimp [ovalFactor, ovalSquared]
    linear_combination hlevel
  have hV5 : ovalProfile a b θ ^ 5 =
      ovalProfile a b θ * ovalSquared a b θ ^ 2 := by
    rw [← hVs]
    ring
  calc
    _ = ovalProfile a b θ / 4 *
        ((b - a) * (Real.cos θ ^ 2 - Real.sin θ ^ 2) *
          Real.sqrt (ovalFactor a b θ) ^ 2 +
          (b - a) ^ 2 * Real.sin θ ^ 2 * Real.cos θ ^ 2) := by
      dsimp [ovalSpeed]
      field_simp
      ring
    _ = ovalProfile a b θ / 4 *
        ((b - a) * (Real.cos θ ^ 2 - Real.sin θ ^ 2) * ovalFactor a b θ +
          (b - a) ^ 2 * Real.sin θ ^ 2 * Real.cos θ ^ 2) := by rw [hKs]
    _ = _ := by rw [hpoly, hV5]; ring

/-- The exact energy level of the parametrized oval. -/
theorem oval_energy {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlevel : a ^ 2 + a * b + b ^ 2 = 1) (θ : ℝ) :
    4 * ovalVelocity a b θ ^ 2 + ovalProfile a b θ ^ 6 -
      ovalProfile a b θ ^ 2 = a ^ 3 - a := by
  have hKs := Real.sq_sqrt (ovalFactor_pos ha hab θ).le
  have hVs := ovalProfile_sq ha hab θ
  have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  have hpoly : (b - a) ^ 2 * Real.sin θ ^ 2 * Real.cos θ ^ 2 *
      ovalFactor a b θ + ovalSquared a b θ ^ 3 - ovalSquared a b θ = a ^ 3 - a := by
    rw [hc]
    dsimp [ovalFactor, ovalSquared]
    linear_combination ((b - a) * Real.sin θ ^ 2) * hlevel
  have hV6 : ovalProfile a b θ ^ 6 = ovalSquared a b θ ^ 3 := by
    rw [← hVs]
    ring
  have hZ : 4 * ovalVelocity a b θ ^ 2 =
      (b - a) ^ 2 * Real.sin θ ^ 2 * Real.cos θ ^ 2 * ovalFactor a b θ := by
    calc
      _ = (b - a) ^ 2 * Real.sin θ ^ 2 * Real.cos θ ^ 2 *
          Real.sqrt (ovalFactor a b θ) ^ 2 := by dsimp [ovalVelocity]; ring
      _ = _ := by rw [hKs]
  rw [hZ, hV6, hVs]
  exact hpoly

end Yamabe3.Analysis.Delaunay
