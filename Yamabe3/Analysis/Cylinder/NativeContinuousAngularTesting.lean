import Yamabe3.Analysis.Cylinder.NativeContinuousAngularApproximation
import Yamabe3.Analysis.Cylinder.NativeHalfEndPhysicalForcing
import Yamabe3.Analysis.UniformElliptic.NativeL2SquareConvergence

/-!
# Actual compact-shell test limits for the same angular fields

The proved physical square-error limit is converted to convergence of
actual integrals against a fixed L2 test on the same shell. The original
normalized half-end forcing is retained through its literal coefficient
-8 identity. No uniform bound is substituted for strong convergence,
and no fixed-shell assertion is promoted to a global weighted estimate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay UniformElliptic
open Poincare.Analysis.Elliptic

/-- Real L2 square-error convergence preserves the actual integral
pairing, with the original representatives and the original measure. -/
theorem integral_mul_tendsto_of_integral_sq_sub
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {fn : ℕ → X → ℝ} {f ψ : X → ℝ}
    (hn : ∀ n, MemLp (fn n) 2 μ) (hf : MemLp f 2 μ)
    (hlim : Tendsto (fun n => ∫ x, (fn n x - f x) ^ 2 ∂μ) atTop (𝓝 0))
    (hψ : MemLp ψ 2 μ) :
    Tendsto (fun n => ∫ x, fn n x * ψ x ∂μ) atTop (𝓝 (∫ x, f x * ψ x ∂μ)) := by
  have h := tendsto_integral_mul_L2 (native_tendsto_toLp_of_integral_sq_sub hn hf hlim) hψ
  have he (n : ℕ) :
      (∫ x, (hn n).toLp (fn n) x * ψ x ∂μ) = ∫ x, fn n x * ψ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [(hn n).coeFn_toLp] with x hx
    rw [hx]
  have he' : (∫ x, hf.toLp f x * ψ x ∂μ) = ∫ x, f x * ψ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  simpa only [he, he'] using h

/-- On one actual shell, every L2 test sees the same physical finite
fields converge to the same jointly measurable infinite representative. -/
theorem native_projectedAngular_lift_pairing_tendsto
    {s : ℕ → Finset AngularIndex} (hs : Tendsto s atTop atTop)
    {U : ℝ → AngularL2} (hU : Continuous U)
    {z : ℝ × S → ℝ} (hz : Measurable z)
    (hae : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ))
    (a b : ℝ) {ψ : E → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict (cylinderShell a b))) :
    Tendsto (fun n => ∫ x in cylinderShell a b,
      cylinderLift (projectedAngular (s n) U) x * ψ x) atTop
      (𝓝 (∫ x in cylinderShell a b, cylinderLift z x * ψ x)) := by
  exact integral_mul_tendsto_of_integral_sq_sub
    (fun n => memLp_projectedAngular_lift_of_continuous (s n) hU a b)
    (memLp_cylinderLift_on_shell hz a b (native_joint_memLp_interval hU hz hae a b))
    (integral_projectedAngular_lift_error_tendsto_of_continuous hs hU hz hae a b) hψ

/-- The original coefficient-eight physical forcing converges against
all L2 tests on the same shell. This uses the true projection error,
not the uniform full-ball source bound. -/
theorem native_projected_halfEnd_physicalForcing_pairing_tendsto
    {s : ℕ → Finset AngularIndex} (hs : Tendsto s atTop atTop)
    {U : ℝ → AngularL2} (hU : Continuous U)
    {z : ℝ × S → ℝ} (hz : Measurable z)
    (hae : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ))
    (a b : ℝ) {ψ : E → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict (cylinderShell a b))) :
    Tendsto (fun n => ∫ x in cylinderShell a b,
      physicalForcing (fun p => Real.exp (-2 * p.1) * projectedAngular (s n) U p) x * ψ x)
      atTop (𝓝 (∫ x in cylinderShell a b,
        physicalForcing (fun p => Real.exp (-2 * p.1) * z p) x * ψ x)) := by
  have h := (native_projectedAngular_lift_pairing_tendsto hs hU hz hae a b hψ).const_mul (-8)
  simp only [physicalForcing_expNegTwo, mul_assoc, integral_const_mul]
  exact h

#check @integral_mul_tendsto_of_integral_sq_sub
#check @native_projectedAngular_lift_pairing_tendsto
#check @native_projected_halfEnd_physicalForcing_pairing_tendsto
#print axioms integral_mul_tendsto_of_integral_sq_sub
#print axioms native_projectedAngular_lift_pairing_tendsto
#print axioms native_projected_halfEnd_physicalForcing_pairing_tendsto

end Yamabe3.Analysis.SpherePolar
