import Yamabe3.Analysis.Cylinder.NativeHalfEndPhysicalForcing
import Yamabe3.Analysis.HilbertFiniteProjectionFilter

/-!
# Actual physical value and source square-error limits for spectral nets

The original same-representative polar comparison is combined with the
actual filter Hilbert error integral.  Both the value and coefficient-eight
physical source therefore converge in true Euclidean L2 along the original
cofinal family.  The source limit retains its exact high projection and
its literal exp(-2t) weight through the already proved factor 64 identity.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay

variable {J : Type*} {l : Filter J} [l.IsCountablyGenerated]

theorem integral_projectedAngular_lift_error_tendsto_filter
    {s : J → Finset AngularIndex} (hs : Tendsto s l atTop)
    {U : ℝ → AngularL2} (hU : Continuous U)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ)) (a b : ℝ) :
    Tendsto (fun j => ∫ x in cylinderShell a b,
      (cylinderLift (projectedAngular (s j) U) x - cylinderLift w x) ^ 2) l (𝓝 0) := by
  have hbound (j : J) : (∫ x in cylinderShell a b,
      (cylinderLift (projectedAngular (s j) U) x - cylinderLift w x) ^ 2) ≤
      Real.exp (-2 * a) * ∫ t in Icc a b,
        ‖finiteHilbertProjection angularBasis (s j) (U t) - U t‖ ^ 2 := by
    have h := integral_cylinderLift_sq_shell_le
      (((continuous_finiteHilbertProjection angularBasis (s j)).comp hU).sub hU)
      ((continuous_projectedAngular (s j) hU).measurable.sub hw)
      (projectedAngular_sub_ae (s j) U hae) a b
    change (∫ x in cylinderShell a b,
      cylinderLift (fun p => projectedAngular (s j) U p - w p) x ^ 2) ≤ _ at h
    rw [cylinderLift_sub] at h
    exact h
  have hlim := (finiteHilbertProjection_integral_error_tendsto_filter
    angularBasis hs hU a b).const_mul (Real.exp (-2 * a))
  simp only [mul_zero] at hlim
  exact squeeze_zero (fun j => integral_nonneg (fun x => sq_nonneg _)) hbound hlim

theorem integral_projected_halfEnd_physicalForcing_error_tendsto_filter
    {s : J → Finset AngularIndex} (hs : Tendsto s l atTop)
    {U : ℝ → AngularL2} (hU : Continuous U)
    {z : ℝ × S → ℝ} (hz : Measurable z)
    (hae : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ)) (a b : ℝ) :
    Tendsto (fun j => ∫ x in cylinderShell a b,
      (physicalForcing (fun p => Real.exp (-2 * p.1) * projectedAngular (s j) U p) x -
        physicalForcing (fun p => Real.exp (-2 * p.1) * z p) x) ^ 2) l (𝓝 0) := by
  have h := (integral_projectedAngular_lift_error_tendsto_filter
    hs hU hz hae a b).const_mul (64 : ℝ)
  simpa only [integral_physicalForcing_expNegTwo_sq_sub, mul_zero] using h

#print axioms integral_projectedAngular_lift_error_tendsto_filter
#print axioms integral_projected_halfEnd_physicalForcing_error_tendsto_filter

end Yamabe3.Analysis.SpherePolar
