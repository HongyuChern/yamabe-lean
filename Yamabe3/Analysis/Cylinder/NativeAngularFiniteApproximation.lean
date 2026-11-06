import Yamabe3.Analysis.Cylinder.NativeCylinderHilbertNorm
import Yamabe3.Analysis.HilbertFiniteProjection

/-!
# Actual Euclidean L2 convergence of finite native angular projections

The same Hilbert curve and its genuine joint representative are retained.
The real finite smooth eigenfunction sums represent the actual orthogonal
projections. The physical square-integral error is bounded by a fixed
shell weight times the proved compact-time Hilbert error integral.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay

def projectedAngular (s : Finset AngularIndex) (U : ℝ → AngularL2) : ℝ × S → ℝ :=
  finiteAngular s (fun i t => inner ℝ (angularBasis i) (U t))

theorem smooth_projectedAngular (s : Finset AngularIndex) {U : ℝ → AngularL2}
    (hU : ∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (U t))) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (projectedAngular s U) :=
  smooth_finiteAngular s _ (fun i _ => hU i)

theorem projectedAngular_ae (s : Finset AngularIndex) (U : ℝ → AngularL2) (t : ℝ) :
    (fun θ => projectedAngular s U (t, θ)) =ᵐ[angularVolume]
      ((finiteHilbertProjection angularBasis s (U t) : AngularL2) : S → ℝ) :=
  finiteAngular_ae s _ t

theorem projectedAngular_sub_ae (s : Finset AngularIndex) (U : ℝ → AngularL2)
    {w : ℝ × S → ℝ}
    (hae : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ)) (t : ℝ) :
    (fun θ => projectedAngular s U (t, θ) - w (t, θ)) =ᵐ[angularVolume]
      (finiteHilbertProjection angularBasis s (U t) - U t : AngularL2) := by
  have hc := (ae_restrict_iff' MeasurableSet.univ).mp
    (Lp.coeFn_sub (finiteHilbertProjection angularBasis s (U t)) (U t))
  filter_upwards [projectedAngular_ae s U t, hae t, hc] with θ hP hU hc
  rw [hP, hU]
  simpa only [Pi.sub_apply] using (hc (mem_univ θ)).symm

theorem cylinderLift_sub (w z : ℝ × S → ℝ) :
    cylinderLift (fun p => w p - z p) = fun x => cylinderLift w x - cylinderLift z x := by
  funext x
  by_cases hx : x = 0
  · subst x
    simp only [cylinderLift_zero, sub_self]
  · let y : puncturedSpace := ⟨x, by change x ≠ 0; exact hx⟩
    have hr : 0 < ‖(y : E)‖ := norm_pos_iff.mpr hx
    change cylinderLift (fun p => w p - z p) (y : E) =
      cylinderLift w (y : E) - cylinderLift z (y : E)
    rw [← norm_smul_sphereDirection y]
    simp only [cylinderLift_smul _ hr, mul_sub]

theorem memLp_projectedAngular_lift (s : Finset AngularIndex) {U : ℝ → AngularL2}
    (hU : Continuous U)
    (hcoeff : ∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (U t))) (a b : ℝ) :
    MemLp (cylinderLift (projectedAngular s U)) 2 (volume.restrict (cylinderShell a b)) := by
  apply memLp_cylinderLift_on_shell (smooth_projectedAngular s hcoeff).continuous.measurable
  exact native_joint_memLp_interval ((continuous_finiteHilbertProjection angularBasis s).comp hU)
    (smooth_projectedAngular s hcoeff).continuous.measurable (projectedAngular_ae s U) a b

theorem integral_projectedAngular_lift_sq_le (s : Finset AngularIndex) {U : ℝ → AngularL2}
    (hU : Continuous U)
    (hcoeff : ∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (U t))) (a b : ℝ) :
    (∫ x in cylinderShell a b, cylinderLift (projectedAngular s U) x ^ 2) ≤
      Real.exp (-2 * a) * ∫ t in Icc a b, ‖U t‖ ^ 2 := by
  apply (integral_cylinderLift_sq_shell_le
    ((continuous_finiteHilbertProjection angularBasis s).comp hU)
    (smooth_projectedAngular s hcoeff).continuous.measurable (projectedAngular_ae s U) a b).trans
  apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  apply integral_mono
    ((((continuous_finiteHilbertProjection angularBasis s).comp hU).norm.pow 2).integrableOn_Icc)
    ((hU.norm.pow 2).integrableOn_Icc)
  intro t
  exact pow_le_pow_left₀ (norm_nonneg _) (finiteHilbertProjection_norm_le angularBasis s (U t)) 2

/-- The actual finite smooth physical functions converge in the true
Euclidean square integral on every shell. The exhaustion is the very same
one as the genuine Hilbert-basis finite projections. -/
theorem integral_projectedAngular_lift_error_tendsto {s : ℕ → Finset AngularIndex}
    (hs : Tendsto s atTop atTop) {U : ℝ → AngularL2} (hU : Continuous U)
    (hcoeff : ∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (U t)))
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
      ((smooth_projectedAngular (s n) hcoeff).continuous.measurable.sub hw)
      (projectedAngular_sub_ae (s n) U hae) a b
    change (∫ x in cylinderShell a b,
      cylinderLift (fun p => projectedAngular (s n) U p - w p) x ^ 2) ≤ _ at h
    rw [cylinderLift_sub] at h
    exact h
  have hlim := (finiteHilbertProjection_integral_error_tendsto angularBasis hs hU a b).const_mul
    (Real.exp (-2 * a))
  simp only [mul_zero] at hlim
  exact squeeze_zero (fun n => integral_nonneg (fun x => sq_nonneg _)) hbound hlim

#print axioms integral_projectedAngular_lift_sq_le
#print axioms integral_projectedAngular_lift_error_tendsto

end Yamabe3.Analysis.SpherePolar
