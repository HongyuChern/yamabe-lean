import Yamabe3.Analysis.Cylinder.NativeFiniteC1PhysicalEquation

/-!
# The same projected C2 field and its actual physical forcing

The generic finite-coefficient theorem is instantiated with the actual
Hilbert coordinates of U and with exp(-2t) times the coordinates of F.
The source cancellation is an equality of the already defined physical
forcing, including its prescribed totalization at zero. This algebraic
identity is global; the differential equations remain restricted to
open subdomains of the punctured unit ball.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay

/-- The literal exp(-2t) cancels the literal physical r^-2 factor. At
the missing origin both sides are zero by the retained lift definition. -/
theorem physicalForcing_expNegTwo (z : ℝ × S → ℝ) (x : E) :
    physicalForcing (fun p => Real.exp (-2 * p.1) * z p) x =
      -8 * cylinderLift z x := by
  by_cases hx : x = 0
  · subst x
    simp only [physicalForcing, cylinderLift_zero, mul_zero, zero_div]
  · let y : puncturedSpace := ⟨x, by change x ≠ 0; exact hx⟩
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have he : Real.exp (-2 * (-Real.log ‖x‖)) = ‖x‖ ^ 2 := by
      rw [show -2 * (-Real.log ‖x‖) = Real.log ‖x‖ + Real.log ‖x‖ by ring,
        Real.exp_add, Real.exp_log hr, pow_two]
    change -8 * cylinderLift (fun p => Real.exp (-2 * p.1) * z p) (y : E) /
      ‖(y : E)‖ ^ 2 = -8 * cylinderLift z (y : E)
    rw [cylinderLift_coe, cylinderLift_coe]
    change -8 * (radialScale ‖x‖ * (Real.exp (-2 * (-Real.log ‖x‖)) *
      z (-Real.log ‖x‖, sphereDirection y))) / ‖x‖ ^ 2 =
        -8 * (radialScale ‖x‖ * z (-Real.log ‖x‖, sphereDirection y))
    rw [he]
    field_simp [hr.ne'] <;> ring

theorem physicalForcing_expNegTwo_div_eight (z : ℝ × S → ℝ) (x : E) :
    physicalForcing (fun p => Real.exp (-2 * p.1) * z p) x / 8 =
      -cylinderLift z x := by
  rw [physicalForcing_expNegTwo]
  ring

/-- Finite angular projection commutes with the same scalar time
weight, without a regularity hypothesis or a change of representative. -/
theorem finiteAngular_expNegTwo_coefficients
    (s : Finset AngularIndex) (F : ℝ → AngularL2) :
    finiteAngular s (fun i t => Real.exp (-2 * t) * inner ℝ (angularBasis i) (F t)) =
      (fun p => Real.exp (-2 * p.1) * projectedAngular s F p) := by
  funext p
  simp only [finiteAngular, projectedAngular, Finset.mul_sum, mul_assoc]

/-- Actual scalar C2 coordinates give the normalized physical weak
equation for the original finite projection of U. The literal forcing
definition is retained in the conclusion. -/
theorem native_projected_c2_physical_weak_equation
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩhalf : Ω ⊆ {x : E | x ≠ 0 ∧ ‖x‖ < 1})
    (V : ℝ → ℝ) (s : Finset AngularIndex) (U F : ℝ → AngularL2)
    (hq : ∀ i ∈ s,
      ContDiffOn ℝ 2 (fun t => inner ℝ (angularBasis i) (U t)) (Ioi 0))
    (heq : ∀ i ∈ s, ∀ t, 0 < t →
      deriv (deriv (fun a => inner ℝ (angularBasis i) (U a))) t =
        (angularEigenvalue i + 1 / 4 - V t) * inner ℝ (angularBasis i) (U t) +
          Real.exp (-2 * t) * inner ℝ (angularBasis i) (F t)) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ j : Fin 3,
        fderiv ℝ (cylinderLift (projectedAngular s U)) x (EuclideanSpace.single j 1) *
          fderiv ℝ φ x (EuclideanSpace.single j 1)) =
        ∫ x in Ω, (physicalForcing
            (fun p => Real.exp (-2 * p.1) * projectedAngular s F p) x / 8 +
          (V (-Real.log ‖x‖) / ‖x‖ ^ 2) * cylinderLift (projectedAngular s U) x) * φ x := by
  simpa only [finitePhysical_eq_lift, finiteAngular_expNegTwo_coefficients, projectedAngular] using
    native_finite_c2_physical_weak_equation hΩ hΩhalf V s
      (fun i t => inner ℝ (angularBasis i) (U t))
      (fun i t => Real.exp (-2 * t) * inner ℝ (angularBasis i) (F t)) hq heq

/-- The original finite projected field has the actual negative
coordinate trace -lift(F_s) + r^-2 V(-log r) lift(U_s). -/
theorem native_projected_c2_physical_negative_trace_eq
    (V : ℝ → ℝ) (s : Finset AngularIndex) (U F : ℝ → AngularL2)
    (hq : ∀ i ∈ s,
      ContDiffOn ℝ 2 (fun t => inner ℝ (angularBasis i) (U t)) (Ioi 0))
    (heq : ∀ i ∈ s, ∀ t, 0 < t →
      deriv (deriv (fun a => inner ℝ (angularBasis i) (U a))) t =
        (angularEigenvalue i + 1 / 4 - V t) * inner ℝ (angularBasis i) (U t) +
          Real.exp (-2 * t) * inner ℝ (angularBasis i) (F t))
    {x : E} (hx : x ≠ 0) (hx1 : ‖x‖ < 1) :
    -(∑ j : Fin 3, fderiv ℝ
      (fun y => fderiv ℝ (cylinderLift (projectedAngular s U)) y
        (EuclideanSpace.single j 1)) x (EuclideanSpace.single j 1)) =
      -cylinderLift (projectedAngular s F) x +
        (V (-Real.log ‖x‖) / ‖x‖ ^ 2) * cylinderLift (projectedAngular s U) x := by
  simpa only [finitePhysical_eq_lift, finiteAngular_expNegTwo_coefficients,
    physicalForcing_expNegTwo_div_eight, projectedAngular] using
    native_finitePhysical_negative_trace_eq V s
      (fun i t => inner ℝ (angularBasis i) (U t))
      (fun i t => Real.exp (-2 * t) * inner ℝ (angularBasis i) (F t)) hq heq hx hx1

/-- The same weak equation after the proved forcing cancellation. The
source and solution are still the original finite projected functions. -/
theorem native_projected_c2_physical_weak_equation_expNegTwo
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩhalf : Ω ⊆ {x : E | x ≠ 0 ∧ ‖x‖ < 1})
    (V : ℝ → ℝ) (s : Finset AngularIndex) (U F : ℝ → AngularL2)
    (hq : ∀ i ∈ s,
      ContDiffOn ℝ 2 (fun t => inner ℝ (angularBasis i) (U t)) (Ioi 0))
    (heq : ∀ i ∈ s, ∀ t, 0 < t →
      deriv (deriv (fun a => inner ℝ (angularBasis i) (U a))) t =
        (angularEigenvalue i + 1 / 4 - V t) * inner ℝ (angularBasis i) (U t) +
          Real.exp (-2 * t) * inner ℝ (angularBasis i) (F t)) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ j : Fin 3,
        fderiv ℝ (cylinderLift (projectedAngular s U)) x (EuclideanSpace.single j 1) *
          fderiv ℝ φ x (EuclideanSpace.single j 1)) =
        ∫ x in Ω, (-cylinderLift (projectedAngular s F) x +
          (V (-Real.log ‖x‖) / ‖x‖ ^ 2) * cylinderLift (projectedAngular s U) x) * φ x := by
  simpa only [physicalForcing_expNegTwo_div_eight] using
    native_projected_c2_physical_weak_equation hΩ hΩhalf V s U F hq heq

#print axioms physicalForcing_expNegTwo
#print axioms finiteAngular_expNegTwo_coefficients
#print axioms native_projected_c2_physical_weak_equation
#print axioms native_projected_c2_physical_negative_trace_eq
#print axioms native_projected_c2_physical_weak_equation_expNegTwo

end Yamabe3.Analysis.SpherePolar
