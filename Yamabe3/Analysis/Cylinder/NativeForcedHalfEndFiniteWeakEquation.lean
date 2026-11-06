import Yamabe3.Analysis.NativeForcedHalfEnd
import Yamabe3.Analysis.Cylinder.NativeProjectedC2PhysicalEquation
import Yamabe3.Analysis.Cylinder.NativeHalfEndCompactTesting

/-!
# The actual forced half-end produces its finite physical weak equations

This file instantiates the proved finite C2 calculation with the actual
constructed native Dirichlet curve and the actual high projection of the
original source.  Both the scalar equation and its needed regularity are
outputs of that construction.  No finite weak equation is an input.

The original physical forcing, its coefficient eight, and the singular
potential `V (-log norm) / norm^2` are kept literally.  Every differential
statement is confined to the punctured unit ball.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Manifold ContDiff Topology RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem halfEnd_puncturedUnitBall_eq :
    Metric.ball (0 : E) 1 \ {(0 : E)} = {x : E | x ≠ 0 ∧ ‖x‖ < 1} := by
  ext x
  simp only [mem_diff, Metric.mem_ball, dist_zero_right, mem_singleton_iff,
    mem_setOf_eq, and_comm]

theorem nativeHalfEndPotentialCoefficient_measurable (V : ℝ →ᵇ ℝ) :
    Measurable (nativeHalfEndPotentialCoefficient V) :=
  (V.continuous.measurable.comp (Real.measurable_log.comp measurable_norm).neg).div
    (measurable_norm.pow_const 2)

theorem nativeHalfEndPotentialCoefficient_norm_le_on_shell
    (V : ℝ →ᵇ ℝ) {a b : ℝ} {x : E} (hx : x ∈ cylinderShell a b) :
    ‖nativeHalfEndPotentialCoefficient V x‖ ≤ ‖V‖ / Real.exp (-b) ^ 2 := by
  have hs : Real.exp (-b) ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos _).le hx.1 2
  rw [nativeHalfEndPotentialCoefficient, norm_div, norm_pow, norm_norm]
  exact (div_le_div_of_nonneg_right (V.norm_coe_le_norm _) (sq_nonneg _)).trans
    (div_le_div_of_nonneg_left (norm_nonneg V) (sq_pos_of_pos (Real.exp_pos _)) hs)

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The same finite field is genuinely C2 on the physical domain. -/
theorem native_forced_halfEnd_finite_lift_contDiffOn_two
    (F : ℝ≥0 →ᵇ AngularL2) (s : Finset AngularIndex) :
    ContDiffOn ℝ 2 (cylinderLift (projectedAngular s
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F)))
      (Metric.ball (0 : E) 1 \ {(0 : E)}) := by
  rw [halfEnd_puncturedUnitBall_eq]
  exact contDiffOn_projectedAngular_lift_of_c2_positive s
    (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F)
    (fun i _ => nativeHalfHighDirichletPhysical_coefficient_c2 hκ0 hκ1 V hV hV0 F i)

/-- Actual finite weak equations on every open physical subdomain. -/
theorem native_forced_halfEnd_finite_weak_equation_on_open
    (F : ℝ≥0 →ᵇ AngularL2) (s : Finset AngularIndex)
    {Ω : Set E} (hΩ : IsOpen Ω)
    (hΩhalf : Ω ⊆ Metric.ball (0 : E) 1 \ {(0 : E)}) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ j : Fin 3,
        fderiv ℝ (cylinderLift (projectedAngular s
          (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))) x
          (EuclideanSpace.single j 1) * fderiv ℝ φ x (EuclideanSpace.single j 1)) =
        ∫ x in Ω, (physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) *
            projectedAngular s (fun t => nativeHighProjection (F t.toNNReal)) p) x / 8 +
          nativeHalfEndPotentialCoefficient V x * cylinderLift (projectedAngular s
            (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F)) x) * φ x := by
  apply native_projected_c2_physical_weak_equation hΩ
    (by simpa only [halfEnd_puncturedUnitBall_eq] using hΩhalf) V s
    (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F)
    (fun t => nativeHighProjection (F t.toNNReal))
  · exact fun i _ => nativeHalfHighDirichletPhysical_coefficient_c2 hκ0 hκ1 V hV hV0 F i
  · exact fun i _ t ht =>
      (nativeHalfHighDirichletPhysical_coefficient_equation hκ0 hκ1 V hV hV0 F i t ht).deriv

/-- The physical finite equation with the original domain, normalization,
source and potential.  This is the direct half-end construction output. -/
theorem native_forced_halfEnd_finite_weak_equation
    (F : ℝ≥0 →ᵇ AngularL2) (s : Finset AngularIndex)
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Metric.ball (0 : E) 1 \ {(0 : E)}) :
    (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)}, ∑ j : Fin 3,
      fderiv ℝ (cylinderLift (projectedAngular s
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))) x
        (EuclideanSpace.single j 1) * fderiv ℝ φ x (EuclideanSpace.single j 1)) =
      ∫ x in Metric.ball (0 : E) 1 \ {(0 : E)},
        (physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) *
          projectedAngular s (fun t => nativeHighProjection (F t.toNNReal)) p) x / 8 +
        nativeHalfEndPotentialCoefficient V x * cylinderLift (projectedAngular s
          (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F)) x) * φ x :=
  native_forced_halfEnd_finite_weak_equation_on_open hκ0 hκ1 V hV hV0 F s
    (Metric.isOpen_ball.sdiff isClosed_singleton) Subset.rfl φ hφ hc hs

#print axioms nativeHalfEndPotentialCoefficient_measurable
#print axioms nativeHalfEndPotentialCoefficient_norm_le_on_shell
#print axioms native_forced_halfEnd_finite_lift_contDiffOn_two
#print axioms native_forced_halfEnd_finite_weak_equation_on_open
#print axioms native_forced_halfEnd_finite_weak_equation

end Yamabe3.Analysis.SpherePolar
