import Yamabe3.Analysis.Cylinder.NativeCylinderLift
import Yamabe3.Analysis.Cylinder.NativePolarTrace
import PoincareLib.Geometry.Riemannian.Curvature.Euclidean
import PoincareLib.Geometry.Riemannian.ScalarOperators.Scaling

/-!
# Actual Euclidean Yamabe operator conjugated to the real cylinder

The native Euclidean Laplacian is conjugated through the explicitly
constructed smooth punctured-space lift.  The angular term is exactly the
native Laplacian of the induced round two-sphere, the same operator whose
actual eigenbasis and low-spectrum gap were proved separately.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open Set Filter PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open Poincare.Geometry.Riemannian.SpaceForm
open Yamabe3.Analysis.Delaunay

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem euclidean_curvatureTensor_zero (x u v w z : E) :
    euclideanD.curvatureTensor x u v w z = 0 := by
  have hc (y a b : E) : euclideanD.connectionCoefficient y a b = 0 := by
    rw [euclideanD.connectionCoefficient_eq_coordinateChristoffel]
    change CoordinateExponential.christoffelBilinear
      (RiemannianMetric.euclideanMetric 3).euclideanCoefficients y a b = 0
    rw [RiemannianMetric.euclideanMetric_christoffel]
    simp
  have he (a b : E) : euclideanD.euclideanConnection a b = fun _ => 0 := by
    funext y
    exact hc y a b
  unfold LeviCivitaData.curvatureTensor
  rw [euclideanD.curvature_eq_euclideanConnection]
  simp only [he, fderiv_const_apply, zero_apply, add_zero,
    sub_self, RiemannianMetric.euclideanMetric_inner, inner_zero_left]

theorem euclidean_scalarCurvature_zero (x : E) : euclideanD.scalarCurvature x = 0 := by
  simp only [LeviCivitaData.scalarCurvature, LeviCivitaData.ricci,
    euclidean_curvatureTensor_zero, Finset.sum_const_zero]

theorem laplacian_cylinderLift {v : ℝ × S → ℝ}
    (hv : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ v)
    {r : ℝ} (hr : 0 < r) (x : S) :
    euclideanD.laplacian (cylinderLift v) (r • (x : E)) = radialScale r / r ^ 2 *
      (deriv (deriv (fun t : ℝ => v (t, x))) (-Real.log r) +
        sphereD.laplacian (fun y : S => v (-Real.log r, y)) x - v (-Real.log r, x) / 4) := by
  have hnorm : ‖r • (x : E)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
  have hne : r • (x : E) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact hr.ne' hnorm.symm
  have hf := contDiffAt_cylinderLift hv hne
  let w : ℝ → ℝ := fun t => v (t, x)
  have hw : ContDiff ℝ ∞ w := smooth_cylinder_time_slice hv x
  have heq : (fun s : ℝ => cylinderLift v (s • (x : E))) =ᶠ[𝓝 r] radialProfile w 0 := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    rw [cylinderLift_smul v hs x]
    simp only [radialProfile, zero_sub, w]
  have hslice : (fun y : S => cylinderLift v (r • (y : E))) =
      fun y => radialScale r * v (-Real.log r, y) := by
    funext y
    exact cylinderLift_smul v hr y
  have h := laplacian_polar hr x hf
  rw [heq.deriv.deriv_eq, heq.deriv_eq, hslice, sphereD.laplacian_const_mul,
    radialProfile_second hw 0 hr, radialProfile_deriv hw 0 hr] at h
  simp only [zero_sub, w] at h
  rw [h]
  field_simp [hr.ne']
  ring

theorem native_yamabe_cylinder_conjugation {v : ℝ × S → ℝ}
    (hv : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ v)
    {r : ℝ} (hr : 0 < r) (x : S) :
    -8 * euclideanD.laplacian (cylinderLift v) (r • (x : E)) +
      euclideanD.scalarCurvature (r • (x : E)) * cylinderLift v (r • (x : E)) -
      6 * cylinderLift v (r • (x : E)) ^ 5 =
      (-8 * radialScale r / r ^ 2) *
        (deriv (deriv (fun t : ℝ => v (t, x))) (-Real.log r) +
          sphereD.laplacian (fun y : S => v (-Real.log r, y)) x -
          v (-Real.log r, x) / 4 + 3 * v (-Real.log r, x) ^ 5 / 4) := by
  have hs5 : radialScale r ^ 5 = radialScale r / r ^ 2 := by
    calc
      radialScale r ^ 5 = radialScale r * (radialScale r ^ 2) ^ 2 := by ring
      _ = radialScale r * (r⁻¹) ^ 2 := by rw [radialScale_sq hr]
      _ = _ := by field_simp [hr.ne']
  rw [euclidean_scalarCurvature_zero, zero_mul, add_zero,
    laplacian_cylinderLift hv hr x, cylinderLift_smul v hr x, mul_pow, hs5]
  ring

theorem native_yamabe_cylinder_conjugation_punctured {v : ℝ × S → ℝ}
    (hv : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ v)
    (x : puncturedSpace) :
    -8 * euclideanD.laplacian (cylinderLift v) (x : E) +
      euclideanD.scalarCurvature (x : E) * cylinderLift v (x : E) -
      6 * cylinderLift v (x : E) ^ 5 =
      (-8 * radialScale ‖(x : E)‖ / ‖(x : E)‖ ^ 2) *
        (deriv (deriv (fun t : ℝ => v (t, sphereDirection x))) (-Real.log ‖(x : E)‖) +
          sphereD.laplacian (fun y : S => v (-Real.log ‖(x : E)‖, y)) (sphereDirection x) -
          v (-Real.log ‖(x : E)‖, sphereDirection x) / 4 +
          3 * v (-Real.log ‖(x : E)‖, sphereDirection x) ^ 5 / 4) := by
  have h := native_yamabe_cylinder_conjugation hv
    (norm_pos_iff.mpr (punctured_ne_zero x)) (sphereDirection x)
  rw [norm_smul_sphereDirection] at h
  exact h

#print axioms euclidean_scalarCurvature_zero
#print axioms laplacian_cylinderLift
#print axioms native_yamabe_cylinder_conjugation
#print axioms native_yamabe_cylinder_conjugation_punctured

end Yamabe3.Analysis.SpherePolar
