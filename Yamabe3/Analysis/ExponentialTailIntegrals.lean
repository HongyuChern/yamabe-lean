import Yamabe3.Analysis.SmoothPeriodicClock
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Genuine half-line primitives for the Delaunay first-mode inverse

The primitives are actual Lebesgue integrals on half-lines. Integrability is
derived from exponential majorants, while differentiation and smoothness
are proved by exact reduction to the ordinary interval primitive.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

/-- The actual left half-line integral. -/
def leftTail (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in Iic t, f s
/-- The actual right half-line integral. -/
def rightTail (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in Ioi t, f s

private theorem leftTail_eq {f : ℝ → ℝ}
    (hint : ∀ t, IntegrableOn f (Iic t)) :
    leftTail f = fun t => leftTail f 0 + timePrimitive f 0 t := by
  funext t
  have h := intervalIntegral.integral_Iic_sub_Iic (hint 0) (hint t)
  change leftTail f t - leftTail f 0 = timePrimitive f 0 t at h
  linarith

private theorem rightTail_eq {f : ℝ → ℝ}
    (hint : ∀ t, IntegrableOn f (Ioi t)) :
    rightTail f = fun t => rightTail f 0 - timePrimitive f 0 t := by
  funext t
  have h := intervalIntegral.integral_Ioi_sub_Ioi' (hint 0) (hint t)
  change rightTail f 0 - rightTail f t = timePrimitive f 0 t at h
  linarith

theorem leftTail_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f)
    (hint : ∀ t, IntegrableOn f (Iic t)) (t : ℝ) :
    HasDerivAt (leftTail f) (f t) t := by
  rw [leftTail_eq hint]
  exact (timePrimitive_hasDerivAt hf 0 t).const_add _

theorem rightTail_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f)
    (hint : ∀ t, IntegrableOn f (Ioi t)) (t : ℝ) :
    HasDerivAt (rightTail f) (-(f t)) t := by
  rw [rightTail_eq hint]
  exact (timePrimitive_hasDerivAt hf 0 t).const_sub _

theorem leftTail_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hint : ∀ t, IntegrableOn f (Iic t)) : ContDiff ℝ ∞ (leftTail f) := by
  rw [leftTail_eq hint]
  exact contDiff_const.add (timePrimitive_contDiff hf 0)

theorem rightTail_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hint : ∀ t, IntegrableOn f (Ioi t)) : ContDiff ℝ ∞ (rightTail f) := by
  rw [rightTail_eq hint]
  exact contDiff_const.sub (timePrimitive_contDiff hf 0)

theorem integrableOn_left_of_exp_bound {f : ℝ → ℝ} (hf : Continuous f)
    {A : ℝ} (hbound : ∀ s, |f s| ≤ A * Real.exp s) (t : ℝ) :
    IntegrableOn f (Iic t) := by
  apply ((integrableOn_exp_Iic t).const_mul A).mono' hf.aestronglyMeasurable.restrict
  exact Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using hbound s

theorem integrableOn_right_of_exp_bound {f : ℝ → ℝ} (hf : Continuous f)
    {A : ℝ} (hbound : ∀ s, |f s| ≤ A * Real.exp (-s)) (t : ℝ) :
    IntegrableOn f (Ioi t) := by
  apply ((integrableOn_exp_neg_Ioi t).const_mul A).mono' hf.aestronglyMeasurable.restrict
  exact Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using hbound s

theorem leftTail_abs_le_of_exp_bound {f : ℝ → ℝ}
    {A : ℝ} (hbound : ∀ s, |f s| ≤ A * Real.exp s) (t : ℝ) :
    |leftTail f t| ≤ A * Real.exp t := by
  have h := norm_integral_le_of_norm_le (f := f) ((integrableOn_exp_Iic t).const_mul A)
    (Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using hbound s)
  simpa only [leftTail, Real.norm_eq_abs, integral_const_mul, integral_exp_Iic] using h

theorem rightTail_abs_le_of_exp_bound {f : ℝ → ℝ}
    {A : ℝ} (hbound : ∀ s, |f s| ≤ A * Real.exp (-s)) (t : ℝ) :
    |rightTail f t| ≤ A * Real.exp (-t) := by
  have h := norm_integral_le_of_norm_le (f := f) ((integrableOn_exp_neg_Ioi t).const_mul A)
    (Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using hbound s)
  simpa only [rightTail, Real.norm_eq_abs, integral_const_mul, integral_exp_neg_Ioi] using h

end Yamabe3.Analysis.Delaunay
