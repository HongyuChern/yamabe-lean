import Yamabe3.Analysis.Cylinder.NativeCylinderLocalL2
import Yamabe3.Analysis.Cylinder.NativeAngularTruncation
import Yamabe3.Analysis.L2JointRepresentative

/-!
# Actual physical square integrals of native Hilbert curves

The representative is assumed to be genuinely jointly measurable, with
the proved slice equality to one native L2 curve. The real logarithmic
polar change of variables then identifies the actual Euclidean shell
square integral. The bounded weight is explicit and independent of a
spectral truncation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem native_joint_memLp_interval {U : ℝ → AngularL2} (hU : Continuous U)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ)) (a b : ℝ) :
    MemLp w 2 ((volume.restrict (Icc a b)).prod angularVolume) := by
  have h := joint_L2_memLp_on_interval hU hw.stronglyMeasurable
    (fun t => ae_restrict_of_ae (s := univ) (hae t)) a b
  simpa only [Measure.restrict_univ] using h

theorem native_joint_integral_sq {U : ℝ → AngularL2} {w : ℝ × S → ℝ}
    (hae : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ)) (t : ℝ) :
    (∫ θ : S, w (t, θ) ^ 2 ∂angularVolume) = ‖U t‖ ^ 2 := by
  have h := joint_L2_integral_sq
    (fun t => ae_restrict_of_ae (s := univ) (hae t)) t
  simpa only [Measure.restrict_univ] using h

theorem integral_cylinderLift_sq_shell_eq {U : ℝ → AngularL2} (hU : Continuous U)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ)) (a b : ℝ) :
    (∫ x in cylinderShell a b, cylinderLift w x ^ 2) =
      ∫ t in Icc a b, Real.exp (-2 * t) * ‖U t‖ ^ 2 := by
  have hL2 := memLp_cylinderLift_on_shell hw a b
    (native_joint_memLp_interval hU hw hae a b)
  have hm : Measurable ((cylinderShell a b).indicator (fun x : E => cylinderLift w x ^ 2)) :=
    ((measurable_cylinderLift hw).pow_const 2).indicator (measurableSet_cylinderShell a b)
  have hi : Integrable ((cylinderShell a b).indicator (fun x : E => cylinderLift w x ^ 2)) :=
    (integrable_indicator_iff (measurableSet_cylinderShell a b)).mpr hL2.integrable_sq
  have hinner (t : ℝ) :
      (∫ θ : S, (Icc a b ×ˢ (univ : Set S)).indicator
        (fun p : ℝ × S => Real.exp (-2 * p.1) * w p ^ 2) (t, θ) ∂angularVolume) =
        (Icc a b).indicator (fun s : ℝ => Real.exp (-2 * s) * ‖U s‖ ^ 2) t := by
    by_cases ht : t ∈ Icc a b
    · rw [Set.indicator_of_mem ht]
      calc
        _ = ∫ θ : S, Real.exp (-2 * t) * w (t, θ) ^ 2 ∂angularVolume := by
          apply integral_congr_ae
          exact Eventually.of_forall fun θ => Set.indicator_of_mem
            (show (t, θ) ∈ Icc a b ×ˢ (univ : Set S) from ⟨ht, mem_univ θ⟩) _
        _ = _ := by rw [integral_const_mul, native_joint_integral_sq hae]
    · rw [Set.indicator_of_notMem ht]
      apply integral_eq_zero_of_ae
      exact Eventually.of_forall fun θ =>
        Set.indicator_of_notMem (fun h => ht h.1) _
  calc
    _ = ∫ x : E, (cylinderShell a b).indicator (fun y : E => cylinderLift w y ^ 2) x :=
      (integral_indicator (measurableSet_cylinderShell a b)).symm
    _ = ∫ t : ℝ, ∫ θ : S, logCylinderWeight
        ((cylinderShell a b).indicator (fun x : E => cylinderLift w x ^ 2)) (t, θ)
          ∂angularVolume := integral_euclidean_eq_cylinder hm hi
    _ = ∫ t : ℝ, (Icc a b).indicator
        (fun s : ℝ => Real.exp (-2 * s) * ‖U s‖ ^ 2) t := by
      simp_rw [logCylinderWeight_shell_square, hinner]
    _ = _ := integral_indicator measurableSet_Icc

/-- A fixed shell gives a single explicit square-integral comparison for
every genuine native Hilbert representative, before any approximation. -/
theorem integral_cylinderLift_sq_shell_le {U : ℝ → AngularL2} (hU : Continuous U)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ)) (a b : ℝ) :
    (∫ x in cylinderShell a b, cylinderLift w x ^ 2) ≤
      Real.exp (-2 * a) * ∫ t in Icc a b, ‖U t‖ ^ 2 := by
  rw [integral_cylinderLift_sq_shell_eq hU hw hae, ← integral_const_mul]
  apply setIntegral_mono_on
    (((show Continuous (fun t : ℝ => Real.exp (-2 * t)) by fun_prop).mul
      (hU.norm.pow 2)).integrableOn_Icc)
    (((hU.norm.pow 2).const_mul _).integrableOn_Icc) measurableSet_Icc
  intro t ht
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (by linarith [ht.1])) (sq_nonneg _)

#print axioms integral_cylinderLift_sq_shell_eq
#print axioms integral_cylinderLift_sq_shell_le

end Yamabe3.Analysis.SpherePolar
