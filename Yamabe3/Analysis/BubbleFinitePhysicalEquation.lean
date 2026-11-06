import Yamabe3.Analysis.Cylinder.NativeFiniteC1PhysicalEquation

/-! Global punctured-space C2 version of the finite physical source
calculation. Derived from the existing all-radius local trace identity;
there is no change to the archived half-ball theorem. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem finitePhysical_contDiffOn_offZero_C2 (s:Finset AngularIndex)
    (q:AngularIndex→ℝ→ℝ) (hq:∀i∈s,ContDiff ℝ 2 (q i)):
    ContDiffOn ℝ 2 (finitePhysical s q) ({0}ᶜ:Set E):=by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  apply ContDiffAt.sum
  intro i hi
  exact contDiffAt_cylinderLift_separable_of_c2 (smooth_angularRepresentative i) hx
    (hq i hi).contDiffAt

theorem native_finitePhysical_negative_trace_eq_global_C2
    (V : ℝ → ℝ) (s : Finset AngularIndex) (q f : AngularIndex → ℝ → ℝ)
    (hq : ∀ i ∈ s, ContDiff ℝ 2 (q i))
    (heq : ∀ i ∈ s, ∀ t,
      deriv (deriv (q i)) t = (angularEigenvalue i + 1 / 4 - V t) * q i t + f i t)
    {x : E} (hx : x ≠ 0) :
    -(∑ j : Fin 3, fderiv ℝ
      (fun y => fderiv ℝ (finitePhysical s q) y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single j 1)) =
      physicalForcing (finiteAngular s f) x / 8 +
        (V (-Real.log ‖x‖) / ‖x‖ ^ 2) * finitePhysical s q x := by
  let y : puncturedSpace := ⟨x, by change x ≠ 0; exact hx⟩
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have htrace := native_finitePhysical_trace_of_c2_at s q hr (sphereDirection y)
    (fun i hi => (hq i hi).contDiffAt)
  rw [norm_smul_sphereDirection y] at htrace
  have hsum : (∑ i ∈ s, (deriv (deriv (q i)) (-Real.log ‖x‖) -
      (angularEigenvalue i + 1 / 4) * q i (-Real.log ‖x‖)) *
        angularRepresentative i (sphereDirection y)) =
      (∑ i ∈ s, f i (-Real.log ‖x‖) * angularRepresentative i (sphereDirection y)) -
        V (-Real.log ‖x‖) *
          (∑ i ∈ s, q i (-Real.log ‖x‖) * angularRepresentative i (sphereDirection y)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [heq i hi _]
    ring
  rw [htrace, hsum, finitePhysical_eq_lift]
  change _ = physicalForcing (finiteAngular s f) (y : E) / 8 +
    (V (-Real.log ‖x‖) / ‖x‖ ^ 2) * cylinderLift (finiteAngular s q) (y : E)
  rw [physicalForcing, cylinderLift_coe, cylinderLift_coe]
  simp only [puncturedCylinderLift, cylinderCoordinates, finiteAngular]
  change _ = (-8 * (radialScale ‖x‖ *
      (∑ i ∈ s, f i (-Real.log ‖x‖) * angularRepresentative i (sphereDirection y))) /
      ‖x‖ ^ 2) / 8 + (V (-Real.log ‖x‖) / ‖x‖ ^ 2) *
      (radialScale ‖x‖ *
        (∑ i ∈ s, q i (-Real.log ‖x‖) * angularRepresentative i (sphereDirection y)))
  ring

#print axioms finitePhysical_contDiffOn_offZero_C2
#print axioms native_finitePhysical_negative_trace_eq_global_C2
end Yamabe3.Analysis.SpherePolar
