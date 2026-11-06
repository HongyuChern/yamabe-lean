import Yamabe3.Analysis.TimeTestEquation

/-! Compact time testing at the regularity actually supplied by the
continuous-source inverse: differentiability twice and continuous ODE
right hand side, without adding smoothness of the source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

theorem compact_time_integration_by_parts_differentiable {ζ u : ℝ → ℝ}
    (hζ : Differentiable ℝ ζ) (hc : HasCompactSupport ζ) (hdζ : Continuous (deriv ζ))
    (hu : Differentiable ℝ u) (hdu : Continuous (deriv u)) :
    (∫ t : ℝ, ζ t*deriv u t)=-(∫ t : ℝ, deriv ζ t*u t) := by
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun t _ => (hζ t).hasDerivAt) (fun t _ => (hu t).hasDerivAt)
    (compact_time_integrable_mul hζ.continuous hc hdu)
    (compact_time_integrable_mul hdζ hc.deriv hu.continuous)
    (compact_time_integrable_mul hζ.continuous hc hu.continuous)

theorem compact_time_second_integration_by_parts_differentiable {ζ u : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ)
    (hu : Differentiable ℝ u) (hdu : Differentiable ℝ (deriv u))
    (hddu : Continuous (deriv (deriv u))) :
    (∫ t : ℝ,ζ t*deriv (deriv u) t)=(∫ t : ℝ,deriv (deriv ζ) t*u t) := by
  have hζ1 := (contDiff_infty_iff_deriv.mp hζ).2
  have hζ2 := (contDiff_infty_iff_deriv.mp hζ1).2
  rw [compact_time_integration_by_parts_differentiable (hζ.differentiable (by simp)) hc hζ1.continuous hdu hddu,
    compact_time_integration_by_parts_differentiable (hζ1.differentiable (by simp)) hc.deriv hζ2.continuous hu hdu.continuous,neg_neg]

theorem second_order_compact_time_test_differentiable {ζ u V F : ℝ → ℝ} {a b : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ) (hu : Differentiable ℝ u) (hdu : Differentiable ℝ (deriv u))
    (hV : Continuous V) (hF : Continuous F)
    (heq : ∀ t, deriv (deriv u) t = b * deriv u t + a * u t + F t - V t * u t) :
    (∫ t : ℝ, deriv (deriv ζ) t * u t) + b * (∫ t : ℝ, deriv ζ t * u t) -
      a * (∫ t : ℝ, ζ t * u t) + (∫ t : ℝ, ζ t * V t * u t) =
        ∫ t : ℝ, ζ t * F t := by
  have hddu : Continuous (deriv (deriv u)) := by
    have he : deriv (deriv u)=(fun t => b*deriv u t+a*u t+F t-V t*u t) := funext heq
    rw [he]
    exact ((continuous_const.mul hdu.continuous).add (continuous_const.mul hu.continuous)).add hF |>.sub (hV.mul hu.continuous)
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
  rw [compact_time_second_integration_by_parts_differentiable hζ hc hu hdu hddu,
    compact_time_integration_by_parts_differentiable (hζ.differentiable (by simp)) hc ((contDiff_infty_iff_deriv.mp hζ).2.continuous) hu hdu.continuous] at he
  linarith only [he]

#print axioms second_order_compact_time_test_differentiable
end Yamabe3.Analysis.Delaunay
