import Yamabe3.Analysis.Cylinder.EuclideanJacobiEnergy
import Yamabe3.Analysis.Cylinder.NativeAngularFiniteApproximation
import Yamabe3.Analysis.Cylinder.CylindricalShellGeometry

/-!
# Actual forcing energy bounds uniform over finite angular projections

The potential is the genuine Euclidean cylindrical Jacobi potential. On a
fixed compact shell its bound is proved from the given smooth radial
profile. The bound is chosen before the finite spectral set and the two
Hilbert curves. This local regularity estimate does not assert uniformity
in the Delaunay neck parameter.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay

def physicalPotential (v : ℝ → ℝ) (x : E) : ℝ :=
  (15 / 4) * cylinderLift (radialCylinder v) x ^ 4

theorem measurable_physicalPotential {v : ℝ → ℝ} (hv : Measurable v) :
    Measurable (physicalPotential v) :=
  measurable_const.mul ((measurable_cylinderLift (hv.comp measurable_fst)).pow_const 4)

theorem contDiffOn_physicalPotential {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) :
    ContDiffOn ℝ ∞ (physicalPotential v) ({0}ᶜ : Set E) := by
  intro x hx
  exact (contDiffAt_const.mul
    ((contDiffAt_cylinderLift (smooth_radialCylinder hv) (by simpa using hx)).pow 4)).contDiffWithinAt

theorem exists_physicalPotential_bound_on_shell {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ cylinderShell a b, ‖physicalPotential v x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_cylinderShell a b).exists_bound_of_continuousOn
    ((contDiffOn_physicalPotential hv).continuousOn.mono (fun _ hx => cylinderShell_ne_zero hx))
  exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩

theorem norm_physicalForcing_div_eight_le_on_shell {f : ℝ × S → ℝ}
    {a b : ℝ} {x : E} (hx : x ∈ cylinderShell a b) :
    ‖physicalForcing f x / 8‖ ≤ (1 / Real.exp (-b) ^ 2) * ‖cylinderLift f x‖ := by
  have hb : 0 < Real.exp (-b) := Real.exp_pos _
  have hsq : Real.exp (-b) ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ hb.le hx.1 2
  calc
    ‖physicalForcing f x / 8‖ = (1 / ‖x‖ ^ 2) * ‖cylinderLift f x‖ := by
      rw [physicalForcing, norm_div, norm_div, norm_mul, norm_pow, norm_norm]
      have h8 : ‖(8 : ℝ)‖ = 8 := by norm_num
      have hn8 : ‖(-8 : ℝ)‖ = 8 := by norm_num
      rw [h8, hn8]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hb) hsq) (norm_nonneg _)

/-- A genuine fixed-shell L2 source estimate. The constant is selected
before the arbitrary solution and forcing representatives. -/
theorem exists_principalForcing_shell_energy_bound {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : E → ℝ) (f : ℝ × S → ℝ),
      MemLp u 2 (volume.restrict (cylinderShell a b)) → Measurable f →
      MemLp f 2 ((volume.restrict (Icc a b)).prod angularVolume) →
      MemLp (physicalPrincipalForcing v u f) 2 (volume.restrict (cylinderShell a b)) ∧
      (∫ x in cylinderShell a b, physicalPrincipalForcing v u f x ^ 2) ≤
        C * ((∫ x in cylinderShell a b, u x ^ 2) +
          ∫ x in cylinderShell a b, cylinderLift f x ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_physicalPotential_bound_on_shell hv a b
  let B : ℝ := 1 / Real.exp (-b) ^ 2
  refine ⟨2 * (B ^ 2 + C ^ 2), by positivity, ?_⟩
  intro u f hu hf hfm
  have hl := memLp_cylinderLift_on_shell hf a b hfm
  have hQ : MemLp (fun x => physicalPotential v x * u x)
      2 (volume.restrict (cylinderShell a b)) := by
    apply hu.of_le_mul (c := C)
      ((measurable_physicalPotential hv.continuous.measurable).aestronglyMeasurable.mul
        hu.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem (measurableSet_cylinderShell a b)] with x hx
    change ‖physicalPotential v x * u x‖ ≤ C * ‖u x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound x hx) (norm_nonneg _)
  have hH : MemLp (fun x => physicalForcing f x / 8)
      2 (volume.restrict (cylinderShell a b)) := by
    apply hl.of_le_mul (c := B)
      ((measurable_physicalForcing hf).div_const 8).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurableSet_cylinderShell a b)] with x hx
    exact norm_physicalForcing_div_eight_le_on_shell hx
  have htotal : MemLp (physicalPrincipalForcing v u f)
      2 (volume.restrict (cylinderShell a b)) := hH.add hQ
  refine ⟨htotal, ?_⟩
  have hiu : 0 ≤ ∫ x in cylinderShell a b, u x ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hif : 0 ≤ ∫ x in cylinderShell a b, cylinderLift f x ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  calc
    _ ≤ ∫ x in cylinderShell a b,
        2 * B ^ 2 * cylinderLift f x ^ 2 + 2 * C ^ 2 * u x ^ 2 := by
      apply setIntegral_mono_on htotal.integrable_sq
        ((hl.integrable_sq.const_mul _).add (hu.integrable_sq.const_mul _))
        (measurableSet_cylinderShell a b)
      intro x hx
      have hp : (physicalForcing f x / 8) ^ 2 ≤ B ^ 2 * cylinderLift f x ^ 2 := by
        have h := pow_le_pow_left₀ (norm_nonneg _)
          (norm_physicalForcing_div_eight_le_on_shell hx (f := f)) 2
        simpa only [mul_pow, Real.norm_eq_abs, sq_abs] using h
      have hq : (physicalPotential v x * u x) ^ 2 ≤ C ^ 2 * u x ^ 2 := by
        have h := pow_le_pow_left₀ (norm_nonneg (physicalPotential v x)) (hbound x hx) 2
        have h' := mul_le_mul_of_nonneg_right h (sq_nonneg (u x))
        simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using h'
      change (physicalForcing f x / 8 + physicalPotential v x * u x) ^ 2 ≤
        2 * B ^ 2 * cylinderLift f x ^ 2 + 2 * C ^ 2 * u x ^ 2
      nlinarith [sq_nonneg (physicalForcing f x / 8 - physicalPotential v x * u x)]
    _ = 2 * B ^ 2 * (∫ x in cylinderShell a b, cylinderLift f x ^ 2) +
        2 * C ^ 2 * (∫ x in cylinderShell a b, u x ^ 2) := by
      rw [integral_add (hl.integrable_sq.const_mul _) (hu.integrable_sq.const_mul _),
        integral_const_mul, integral_const_mul]
    _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg B) hiu, mul_nonneg (sq_nonneg C) hif]

/-- Actual finite projections supply a common forcing-energy bound on a
fixed physical shell; no estimate depends on the selected finite set. -/
theorem exists_finite_principalForcing_energy_bound {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset AngularIndex) (U F : ℝ → AngularL2),
      Continuous U → Continuous F →
      (∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (U t))) →
      (∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (F t))) →
      MemLp (physicalPrincipalForcing v (cylinderLift (projectedAngular s U))
        (projectedAngular s F)) 2 (volume.restrict (cylinderShell a b)) ∧
      (∫ x in cylinderShell a b,
        physicalPrincipalForcing v (cylinderLift (projectedAngular s U)) (projectedAngular s F) x ^ 2) ≤
      C * ((∫ t in Icc a b, ‖U t‖ ^ 2) + ∫ t in Icc a b, ‖F t‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_principalForcing_shell_energy_bound hv a b
  refine ⟨C * Real.exp (-2 * a), mul_nonneg hC (Real.exp_pos _).le, ?_⟩
  intro s U F hU hF hcu hcf
  obtain ⟨hm, hi⟩ := hbound (cylinderLift (projectedAngular s U)) (projectedAngular s F)
    (memLp_projectedAngular_lift s hU hcu a b)
    (smooth_projectedAngular s hcf).continuous.measurable
    (native_joint_memLp_interval ((continuous_finiteHilbertProjection angularBasis s).comp hF)
      (smooth_projectedAngular s hcf).continuous.measurable (projectedAngular_ae s F) a b)
  refine ⟨hm, hi.trans ?_⟩
  calc
    _ ≤ C * (Real.exp (-2 * a) * (∫ t in Icc a b, ‖U t‖ ^ 2) +
        Real.exp (-2 * a) * (∫ t in Icc a b, ‖F t‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (integral_projectedAngular_lift_sq_le s hU hcu a b)
        (integral_projectedAngular_lift_sq_le s hF hcf a b)) hC
    _ = _ := by ring

#print axioms exists_principalForcing_shell_energy_bound
#print axioms exists_finite_principalForcing_energy_bound

end Yamabe3.Analysis.SpherePolar
