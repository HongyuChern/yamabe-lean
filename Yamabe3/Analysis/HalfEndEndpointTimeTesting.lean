import Yamabe3.Analysis.TimeTestEquation
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Actual compact half-end tests with the entrance boundary term

Tests may be nonzero at the entrance. The genuine improper FTC uses
the continuous endpoint value and derivatives only at positive times.
Compact support of the test proves the tail is zero and all integrals
exist. The Cauchy equation then gives both actual entrance terms, with
the sign retained. The second-order theorem explicitly retains the
right derivative of the same value curve at zero.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Yamabe3.Analysis.Delaunay

/-- Actual integration by parts on the positive half-line. The test
may have a nonzero value at zero; no negative-time derivative is used. -/
theorem halfEnd_endpoint_compact_time_integration_by_parts {ζ u du : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ)
    (hu : Continuous u) (hdu : Continuous du)
    (hd : ∀ t : ℝ, 0 < t → HasDerivAt u (du t) t) :
    (∫ t in Ioi (0 : ℝ), ζ t * du t) =
      -ζ 0 * u 0 - (∫ t in Ioi (0 : ℝ), deriv ζ t * u t) := by
  have hdζ := (contDiff_infty_iff_deriv.mp hζ).2
  have hi1 := (compact_time_integrable_mul hdζ.continuous hc.deriv hu).integrableOn
    (s := Ioi (0 : ℝ))
  have hi2 := (compact_time_integrable_mul hζ.continuous hc hdu).integrableOn
    (s := Ioi (0 : ℝ))
  have hsupport : HasCompactSupport (fun t : ℝ => ζ t * u t) := hc.mul_right
  have htail : Tendsto (fun t : ℝ => ζ t * u t) atTop (𝓝 0) := by
    rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at hsupport
    exact (hsupport.filter_mono _root_.atTop_le_cocompact).tendsto
  have hderiv (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      HasDerivAt (fun s => ζ s * u s) (deriv ζ t * u t + ζ t * du t) t := by
    exact ((hζ.differentiable (by simp) t).hasDerivAt).mul (hd t ht)
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (hζ.continuous.mul hu).continuousAt.continuousWithinAt hderiv (hi1.add hi2) htail
  rw [integral_add hi1 hi2, zero_sub] at hFTC
  simp only [Pi.mul_apply] at hFTC
  linarith only [hFTC]

/-- The transposed equation for the same actual Cauchy pair, including
the entrance values. The value derivative at zero is explicitly the
right derivative on Ici zero; no arbitrary boundary datum is supplied. -/
theorem halfEnd_second_order_endpoint_time_test {ζ u du V F : ℝ → ℝ} {a β : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ)
    (hu : Continuous u) (hdu : Continuous du) (hV : Continuous V) (hF : Continuous F)
    (hd : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt u (du t) (Ici 0) t)
    (hdd : ∀ t : ℝ, 0 < t →
      HasDerivAt du (β * du t + a * u t + F t - V t * u t) t) :
    (∫ t in Ioi (0 : ℝ), deriv (deriv ζ) t * u t) +
      β * (∫ t in Ioi (0 : ℝ), deriv ζ t * u t) -
      a * (∫ t in Ioi (0 : ℝ), ζ t * u t) +
      (∫ t in Ioi (0 : ℝ), ζ t * V t * u t) =
        (∫ t in Ioi (0 : ℝ), ζ t * F t) +
          ζ 0 * du 0 - deriv ζ 0 * u 0 - β * ζ 0 * u 0 := by
  have hdopen (t : ℝ) (ht : 0 < t) : HasDerivAt u (du t) t :=
    (hd t ht.le).hasDerivAt (Ici_mem_nhds ht)
  have hdζ := (contDiff_infty_iff_deriv.mp hζ).2
  have hiD := (compact_time_integrable_mul hζ.continuous hc hdu).integrableOn
    (s := Ioi (0 : ℝ))
  have hiU := (compact_time_integrable_mul hζ.continuous hc hu).integrableOn
    (s := Ioi (0 : ℝ))
  have hiF := (compact_time_integrable_mul hζ.continuous hc hF).integrableOn
    (s := Ioi (0 : ℝ))
  have hiV : IntegrableOn (fun t => ζ t * V t * u t) (Ioi (0 : ℝ)) := by
    simpa only [Pi.mul_apply, mul_assoc] using
      (compact_time_integrable_mul hζ.continuous hc (hV.mul hu)).integrableOn
        (s := Ioi (0 : ℝ))
  have hddc : Continuous (fun t => β * du t + a * u t + F t - V t * u t) :=
    (((continuous_const.mul hdu).add (continuous_const.mul hu)).add hF).sub (hV.mul hu)
  have h2 := halfEnd_endpoint_compact_time_integration_by_parts hζ hc hdu hddc hdd
  have h1 := halfEnd_endpoint_compact_time_integration_by_parts
    hdζ hc.deriv hu hdu hdopen
  rw [h1] at h2
  have hpoint : (fun t : ℝ => ζ t * (β * du t + a * u t + F t - V t * u t)) =
      fun t => β * (ζ t * du t) + a * (ζ t * u t) + ζ t * F t - ζ t * V t * u t := by
    funext t
    ring
  have hi1 : IntegrableOn (fun t : ℝ => β * (ζ t * du t) + a * (ζ t * u t))
      (Ioi (0 : ℝ)) := by
    convert (hiD.const_mul β).add (hiU.const_mul a) using 1 <;> rfl
  have hi2 : IntegrableOn (fun t : ℝ => β * (ζ t * du t) + a * (ζ t * u t) + ζ t * F t)
      (Ioi (0 : ℝ)) := by
    convert hi1.add hiF using 1 <;> rfl
  rw [hpoint, integral_sub hi2 hiV, integral_add hi1 hiF,
    integral_add (hiD.const_mul β) (hiU.const_mul a), integral_const_mul, integral_const_mul] at h2
  rw [halfEnd_endpoint_compact_time_integration_by_parts hζ hc hu hdu hdopen] at h2
  linarith only [h2]

#print axioms halfEnd_endpoint_compact_time_integration_by_parts
#print axioms halfEnd_second_order_endpoint_time_test

end Yamabe3.Analysis.Delaunay
