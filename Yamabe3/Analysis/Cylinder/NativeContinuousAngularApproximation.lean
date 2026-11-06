import Yamabe3.Analysis.Cylinder.NativeAngularFiniteApproximation

/-!
# Actual physical L2 approximation for continuous native angular curves

Finite native eigenfunction sums are jointly continuous whenever the
original Hilbert curve is continuous.  This is the only measurability
input required for the real polar-coordinate square-error estimate.
One fixed exhaustive sequence therefore approximates the same chosen
joint representative in the actual Euclidean L2 norm on every shell.
No smoothness of the source coefficients is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem continuous_projectedAngular (s : Finset AngularIndex) {U : ℝ → AngularL2}
    (hU : Continuous U) : Continuous (projectedAngular s U) := by
  unfold projectedAngular finiteAngular
  apply continuous_finsetSum
  intro i hi
  exact (((innerSL ℝ (angularBasis i)).continuous.comp hU).comp continuous_fst).mul
    ((smooth_angularRepresentative i).continuous.comp continuous_snd)

theorem memLp_projectedAngular_lift_of_continuous
    (s : Finset AngularIndex) {U : ℝ → AngularL2} (hU : Continuous U) (a b : ℝ) :
    MemLp (cylinderLift (projectedAngular s U)) 2 (volume.restrict (cylinderShell a b)) := by
  apply memLp_cylinderLift_on_shell (continuous_projectedAngular s hU).measurable
  exact native_joint_memLp_interval ((continuous_finiteHilbertProjection angularBasis s).comp hU)
    (continuous_projectedAngular s hU).measurable (projectedAngular_ae s U) a b

theorem integral_projectedAngular_lift_sq_le_of_continuous
    (s : Finset AngularIndex) {U : ℝ → AngularL2} (hU : Continuous U) (a b : ℝ) :
    (∫ x in cylinderShell a b, cylinderLift (projectedAngular s U) x ^ 2) ≤
      Real.exp (-2 * a) * ∫ t in Icc a b, ‖U t‖ ^ 2 := by
  apply (integral_cylinderLift_sq_shell_le
    ((continuous_finiteHilbertProjection angularBasis s).comp hU)
    (continuous_projectedAngular s hU).measurable (projectedAngular_ae s U) a b).trans
  apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  apply integral_mono
    ((((continuous_finiteHilbertProjection angularBasis s).comp hU).norm.pow 2).integrableOn_Icc)
    ((hU.norm.pow 2).integrableOn_Icc)
  intro t
  exact pow_le_pow_left₀ (norm_nonneg _) (finiteHilbertProjection_norm_le angularBasis s (U t)) 2

/-- The finite physical fields converge to the lift of the same original
joint representative along the same fixed finite spectral exhaustion. -/
theorem integral_projectedAngular_lift_error_tendsto_of_continuous
    {s : ℕ → Finset AngularIndex} (hs : Tendsto s atTop atTop)
    {U : ℝ → AngularL2} (hU : Continuous U)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ)) (a b : ℝ) :
    Tendsto (fun n => ∫ x in cylinderShell a b,
      (cylinderLift (projectedAngular (s n) U) x - cylinderLift w x) ^ 2) atTop (𝓝 0) := by
  have hbound (n : ℕ) : (∫ x in cylinderShell a b,
      (cylinderLift (projectedAngular (s n) U) x - cylinderLift w x) ^ 2) ≤
      Real.exp (-2 * a) * ∫ t in Icc a b,
        ‖finiteHilbertProjection angularBasis (s n) (U t) - U t‖ ^ 2 := by
    have h := integral_cylinderLift_sq_shell_le
      (((continuous_finiteHilbertProjection angularBasis (s n)).comp hU).sub hU)
      ((continuous_projectedAngular (s n) hU).measurable.sub hw)
      (projectedAngular_sub_ae (s n) U hae) a b
    change (∫ x in cylinderShell a b,
      cylinderLift (fun p => projectedAngular (s n) U p - w p) x ^ 2) ≤ _ at h
    rw [cylinderLift_sub] at h
    exact h
  have hlim := (finiteHilbertProjection_integral_error_tendsto angularBasis hs hU a b).const_mul
    (Real.exp (-2 * a))
  simp only [mul_zero] at hlim
  exact squeeze_zero (fun n => integral_nonneg (fun x => sq_nonneg _)) hbound hlim

/-- A single continuous Hilbert curve and one actual joint representative
give its physical L2 value on every shell, before taking any limit. -/
theorem memLp_continuous_angular_lift
    {U : ℝ → AngularL2} (hU : Continuous U)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ)) (a b : ℝ) :
    MemLp (cylinderLift w) 2 (volume.restrict (cylinderShell a b)) :=
  memLp_cylinderLift_on_shell hw a b (native_joint_memLp_interval hU hw hae a b)

#print axioms continuous_projectedAngular
#print axioms memLp_projectedAngular_lift_of_continuous
#print axioms integral_projectedAngular_lift_sq_le_of_continuous
#print axioms integral_projectedAngular_lift_error_tendsto_of_continuous
#print axioms memLp_continuous_angular_lift

end Yamabe3.Analysis.SpherePolar
