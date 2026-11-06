import Yamabe3.Analysis.HalfEndScalarCoercivity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum

/-!
# Scalar estimates for the actual high half-end boundary form

These estimates remove the literal exponential weight, close its decay
at infinity, and retain a quantitative gap for angular eigenvalues at
least six. They do not identify the spectral half-order quadratic form
with a geometric boundary quotient norm.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

open Set Filter
open scoped Topology

namespace Yamabe3.Analysis.Delaunay

/-- The squared positive root used for the actual high-mode ODE. -/
theorem highMode_coercivity_gap_sq (ell : ℝ) (hell : 6 ≤ ell) :
    Real.sqrt (ell - 7 / 2) ^ 2 = ell - 7 / 2 :=
  Real.sq_sqrt (by linarith)

/-- A fixed quantitative loss of one half from the radial conformal
factor leaves a positive half-order spectral gap. -/
theorem highMode_coercivity_gap_lower (ell : ℝ) (hell : 6 ≤ ell) :
    Real.sqrt (1 + ell) / 4 ≤ Real.sqrt (ell - 7 / 2) - 1 / 2 := by
  have hbase : 0 ≤ 1 + ell := by linarith
  have hsquare : (Real.sqrt (1 + ell) / 2) ^ 2 ≤ ell - 7 / 2 := by
    rw [div_pow, Real.sq_sqrt hbase]
    norm_num
    linarith
  have hhalf : Real.sqrt (1 + ell) / 2 ≤ Real.sqrt (ell - 7 / 2) :=
    Real.le_sqrt_of_sq_le hsquare
  have htwo : 2 ≤ Real.sqrt (1 + ell) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hell])
  linarith

/-- The actual radial `1/2` term has the stated negative sign after the
scalar entrance estimate is applied to the same value and derivative. -/
theorem highMode_normal_coercivity_of_scalar
    (ell x dx : ℝ) (hell : 6 ≤ ell)
    (hscalar : Real.sqrt (ell - 7 / 2) * x ^ 2 ≤ -dx * x) :
    (Real.sqrt (1 + ell) / 4) * x ^ 2 ≤ -(dx + (1 / 2 : ℝ) * x) * x := by
  have hgap := mul_le_mul_of_nonneg_right
    (highMode_coercivity_gap_lower ell hell) (sq_nonneg x)
  nlinarith only [hscalar, hgap]

/-- A bound in the actual common exponential weight implies decay of
that very normed-space curve on the positive half-line. -/
theorem halfEnd_tendsto_zero_of_expTwo_bound
    {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (C : ℝ)
    (hbound : ∀ t : ℝ, 0 ≤ t → Real.exp (2 * t) * ‖f t‖ ≤ C) :
    Tendsto f atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => Real.exp (-2 * t) * C) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0))).mul_const C
    simpa only [Function.comp_apply, id_eq, zero_mul] using h
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h := mul_le_mul_of_nonneg_left (hbound t ht) (Real.exp_pos (-2 * t)).le
  have he : Real.exp (-2 * t) * Real.exp (2 * t) = 1 := by
    rw [← Real.exp_add, show -2 * t + 2 * t = 0 by ring, Real.exp_zero]
  simpa only [← mul_assoc, he, one_mul] using h

/-- Removing the same `exp(2t)` weight converts the actual coordinate
equation into `z'' = q z`. The derivative `dz` is identified by actual
derivative uniqueness, rather than chosen as a second independent curve.
Only positive times are used in this second-derivative assertion. -/
theorem halfEnd_expTwo_physical_derivative_equation
    (y z dz q : ℝ → ℝ)
    (hzy : ∀ t : ℝ, 0 < t → z t = Real.exp (-2 * t) * y t)
    (hz : ∀ t : ℝ, 0 < t → HasDerivAt z (dz t) t)
    (hy : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ y t ∧
      HasDerivAt (deriv y) (4 * deriv y t + (q t - 4) * y t) t)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt dz (q t * z t) t := by
  let e : ℝ → ℝ := fun s => Real.exp (-2 * s)
  have he (s : ℝ) : HasDerivAt e (-2 * e s) s := by
    apply (((hasDerivAt_id s).const_mul (-2)).exp).congr_deriv
    dsimp only [e, id_eq]
    ring
  have hdz (s : ℝ) (hs : 0 < s) : dz s = e s * (deriv y s - 2 * y s) := by
    have heq : z =ᶠ[𝓝 s] fun r => e r * y r := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
      exact hzy r hr
    have hd := ((he s).mul (hy s hs).1.hasDerivAt).congr_of_eventuallyEq heq
    calc
      dz s = (-2 * e s) * y s + e s * deriv y s := (hz s hs).unique hd
      _ = e s * (deriv y s - 2 * y s) := by ring
  have hdeq : dz =ᶠ[𝓝 t] fun s => e s * (deriv y s - 2 * y s) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact hdz s hs
  have hd := (he t).mul ((hy t ht).2.sub ((hy t ht).1.hasDerivAt.const_mul 2))
  apply (hd.congr_of_eventuallyEq hdeq).congr_deriv
  rw [hzy t ht]
  dsimp only [e, Pi.sub_apply]
  ring

#print axioms highMode_coercivity_gap_lower
#print axioms highMode_normal_coercivity_of_scalar
#print axioms halfEnd_tendsto_zero_of_expTwo_bound
#print axioms halfEnd_expTwo_physical_derivative_equation

end Yamabe3.Analysis.Delaunay
