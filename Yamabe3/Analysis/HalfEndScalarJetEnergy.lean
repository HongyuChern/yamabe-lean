import Yamabe3.Analysis.HalfEndScalarFourthDerivative
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Literal time-derivative energies through order four. Only the already
proved value and first-derivative energies are needed; higher solution
regularity and energies follow from the actual ODE and coefficient jets. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

private theorem integral_square_domination {f u v : ℝ → ℝ} {A B : ℝ}
    (hf : ContinuousOn f (Ioi 0))
    (hu : IntegrableOn (fun t => u t^2) (Ioi 0))
    (hv : IntegrableOn (fun t => v t^2) (Ioi 0))
    (hb : ∀ t ∈ Ioi 0, f t^2 ≤ A*u t^2+B*v t^2) :
    IntegrableOn (fun t => f t^2) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, f t^2) ≤
        A*(∫ t : ℝ in Ioi 0, u t^2)+B*(∫ t : ℝ in Ioi 0, v t^2) := by
  have hm := (hu.const_mul A).add (hv.const_mul B)
  have hi : IntegrableOn (fun t => f t^2) (Ioi 0) := by
    apply hm.mono' ((hf.pow 2).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hb t ht
  refine ⟨hi, ?_⟩
  have h := integral_mono_ae hi hm (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hb t ht)
  simpa only [integral_add' (hu.const_mul A) (hv.const_mul B), integral_const_mul] using h

theorem scalar_ode_higher_jet_energy
    {z q : ℝ → ℝ} (hz : ContDiffOn ℝ 2 z (Ioi 0)) (hq : ContDiffOn ℝ 2 q (Ioi 0))
    (heq : ∀ t ∈ Ioi 0, deriv (deriv z) t = q t*z t)
    (hzI : IntegrableOn (fun t => z t^2) (Ioi 0))
    (hdI : IntegrableOn (fun t => deriv z t^2) (Ioi 0))
    (W K : ℝ)
    (hq0 : ∀ t ∈ Ioi 0, q t^2 ≤ W^4)
    (hq1 : ∀ t ∈ Ioi 0, deriv q t^2 ≤ K^2)
    (hq2 : ∀ t ∈ Ioi 0, deriv (deriv q) t^2 ≤ K^2) :
    ContDiffOn ℝ 4 z (Ioi 0) ∧
    (IntegrableOn (fun t => deriv (deriv z) t^2) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, deriv (deriv z) t^2) ≤
        W^4*(∫ t : ℝ in Ioi 0, z t^2)) ∧
    (IntegrableOn (fun t => deriv (deriv (deriv z)) t^2) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, deriv (deriv (deriv z)) t^2) ≤
        2*K^2*(∫ t : ℝ in Ioi 0, z t^2)+2*W^4*(∫ t : ℝ in Ioi 0, deriv z t^2)) ∧
    (IntegrableOn (fun t => deriv (deriv (deriv (deriv z))) t^2) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, deriv (deriv (deriv (deriv z))) t^2) ≤
        3*(K^2+W^8)*(∫ t : ℝ in Ioi 0, z t^2)+12*K^2*(∫ t : ℝ in Ioi 0, deriv z t^2)) := by
  have hc4 := scalar_ode_C4_on_open isOpen_Ioi hz hq heq
  have hc3 : ContDiffOn ℝ 3 (deriv z) (Ioi 0) := hc4.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hc2 : ContDiffOn ℝ 2 (deriv (deriv z)) (Ioi 0) := hc3.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hc1 : ContDiffOn ℝ 1 (deriv (deriv (deriv z))) (Ioi 0) := hc2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hc0 : ContDiffOn ℝ 0 (deriv (deriv (deriv (deriv z)))) (Ioi 0) := hc1.deriv_of_isOpen isOpen_Ioi (by norm_num)
  refine ⟨hc4, ?_, ?_, ?_⟩
  · have h := integral_square_domination (A := W^4) (B := 0) hc2.continuousOn hzI hdI (by
      intro t ht
      rw [heq t ht, mul_pow, zero_mul, add_zero]
      exact mul_le_mul_of_nonneg_right (hq0 t ht) (sq_nonneg _))
    simpa only [zero_mul, add_zero] using h
  · apply integral_square_domination hc1.continuousOn hzI hdI
    intro t ht
    rw [scalar_ode_third_derivative isOpen_Ioi hz hq heq ht]
    have h1 := mul_le_mul_of_nonneg_right (hq1 t ht) (sq_nonneg (z t))
    have h2 := mul_le_mul_of_nonneg_right (hq0 t ht) (sq_nonneg (deriv z t))
    nlinarith only [h1,h2,sq_nonneg (deriv q t*z t-q t*deriv z t)]
  · apply integral_square_domination hc0.continuousOn hzI hdI
    intro t ht
    rw [scalar_ode_fourth_derivative isOpen_Ioi hz hq heq ht]
    have h1 := mul_le_mul_of_nonneg_right (hq2 t ht) (sq_nonneg (z t))
    have h2 := mul_le_mul_of_nonneg_right (hq1 t ht) (sq_nonneg (deriv z t))
    have hq4 : q t^4 ≤ W^8 := by
      have h := mul_self_le_mul_self (sq_nonneg (q t)) (hq0 t ht)
      nlinarith only [h]
    have h3 := mul_le_mul_of_nonneg_right hq4 (sq_nonneg (z t))
    nlinarith only [h1,h2,h3,
      sq_nonneg (deriv (deriv q) t*z t-2*deriv q t*deriv z t),
      sq_nonneg (2*deriv q t*deriv z t-q t^2*z t),
      sq_nonneg (deriv (deriv q) t*z t-q t^2*z t)]

#print axioms scalar_ode_higher_jet_energy
end Yamabe3.Analysis.Delaunay
