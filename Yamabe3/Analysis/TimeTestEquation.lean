import Yamabe3.Analysis.DelaunayWeightedInverse
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Genuine time testing of the second-order equation

Both integrations by parts use actual Lebesgue integrals. Compact support
of the smooth test and its derivatives proves every required integrability
statement; boundary terms are not postulated.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

theorem compact_time_integrable_mul {ζ u : ℝ → ℝ}
    (hζ : Continuous ζ) (hc : HasCompactSupport ζ) (hu : Continuous u) :
    Integrable (fun t => ζ t * u t) :=
  (hζ.mul hu).integrable_of_hasCompactSupport hc.mul_right

theorem compact_time_integration_by_parts {ζ u : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ) (hu : ContDiff ℝ ∞ u) :
    (∫ t : ℝ, ζ t * deriv u t) = -(∫ t : ℝ, deriv ζ t * u t) := by
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have hdζ := (contDiff_infty_iff_deriv.mp hζ).2
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun t _ => (hζ.differentiable (by simp) t).hasDerivAt)
    (fun t _ => (hu.differentiable (by simp) t).hasDerivAt)
    (compact_time_integrable_mul hζ.continuous hc hdu.continuous)
    (compact_time_integrable_mul hdζ.continuous hc.deriv hu.continuous)
    (compact_time_integrable_mul hζ.continuous hc hu.continuous)

theorem compact_time_second_integration_by_parts {ζ u : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ) (hu : ContDiff ℝ ∞ u) :
    (∫ t : ℝ, ζ t * deriv (deriv u) t) = (∫ t : ℝ, deriv (deriv ζ) t * u t) := by
  rw [compact_time_integration_by_parts hζ hc (contDiff_infty_iff_deriv.mp hu).2,
    compact_time_integration_by_parts (contDiff_infty_iff_deriv.mp hζ).2 hc.deriv hu,
    neg_neg]

/-- The exact transposed time identity, including the drift sign. -/
theorem second_order_compact_time_test {ζ u V F : ℝ → ℝ} {a b : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ) (hu : ContDiff ℝ ∞ u)
    (hV : Continuous V) (hF : Continuous F)
    (heq : ∀ t, deriv (deriv u) t = b * deriv u t + a * u t + F t - V t * u t) :
    (∫ t : ℝ, deriv (deriv ζ) t * u t) + b * (∫ t : ℝ, deriv ζ t * u t) -
      a * (∫ t : ℝ, ζ t * u t) + (∫ t : ℝ, ζ t * V t * u t) =
        ∫ t : ℝ, ζ t * F t := by
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have hiD := compact_time_integrable_mul hζ.continuous hc hdu.continuous
  have hiU := compact_time_integrable_mul hζ.continuous hc hu.continuous
  have hiF := compact_time_integrable_mul hζ.continuous hc hF
  have hiV : Integrable (fun t => ζ t * V t * u t) := by
    simpa only [Pi.mul_apply, mul_assoc] using compact_time_integrable_mul hζ.continuous hc (hV.mul hu.continuous)
  have hpoint : (fun t : ℝ => ζ t * deriv (deriv u) t) =
      fun t => b * (ζ t * deriv u t) + a * (ζ t * u t) + ζ t * F t - ζ t * V t * u t := by
    funext t
    rw [heq]
    ring
  have hi1 : Integrable (fun t : ℝ => b * (ζ t * deriv u t) + a * (ζ t * u t)) := by
    convert (hiD.const_mul b).add (hiU.const_mul a) using 1 <;> rfl
  have hi2 : Integrable (fun t : ℝ => b * (ζ t * deriv u t) + a * (ζ t * u t) + ζ t * F t) := by
    convert hi1.add hiF using 1 <;> rfl
  have he : (∫ t : ℝ, ζ t * deriv (deriv u) t) =
      b * (∫ t : ℝ, ζ t * deriv u t) + a * (∫ t : ℝ, ζ t * u t) +
        (∫ t : ℝ, ζ t * F t) - (∫ t : ℝ, ζ t * V t * u t) := by
    rw [hpoint, integral_sub hi2 hiV,
      integral_add hi1 hiF,
      integral_add (hiD.const_mul b) (hiU.const_mul a), integral_const_mul, integral_const_mul]
  rw [compact_time_second_integration_by_parts hζ hc hu,
    compact_time_integration_by_parts hζ hc hu] at he
  linarith only [he]

end Yamabe3.Analysis.Delaunay
