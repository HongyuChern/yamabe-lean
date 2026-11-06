import Yamabe3.Analysis.Cylinder.NativeCylinderConjugation
import Yamabe3.Analysis.Cylinder.NativeYamabeVariation

/-!
# Genuine nonseparated cylinder linearization

The real first variation of the native Euclidean Yamabe residual is
conjugated to the operator with the actual induced sphere Laplacian.
The perturbation is any jointly smooth cylinder function, not a single
angular eigenmode.  This supplies the geometric meaning of the scalar
mode inverses after their native angular reconstruction.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open Poincare.Geometry.Riemannian.SpaceForm
open Yamabe3.Analysis.Delaunay Yamabe3.Analysis.YamabeVariation

theorem native_yamabe_linearized_cylinder (v : ℝ → ℝ) {w : ℝ × S → ℝ}
    (hw : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ w)
    {r : ℝ} (hr : 0 < r) (x : S) :
    -8 * euclideanD.laplacian (cylinderLift w) (r • (x : E)) +
      euclideanD.scalarCurvature (r • (x : E)) * cylinderLift w (r • (x : E)) -
      30 * radialProfile v 0 r ^ 4 * cylinderLift w (r • (x : E)) =
      (-8 * radialScale r / r ^ 2) *
        (deriv (deriv (fun t : ℝ => w (t, x))) (-Real.log r) +
          sphereD.laplacian (fun y : S => w (-Real.log r, y)) x - w (-Real.log r, x) / 4 +
          (15 / 4 : ℝ) * v (-Real.log r) ^ 4 * w (-Real.log r, x)) := by
  have hs4 : radialScale r ^ 4 = (r ^ 2)⁻¹ := by
    rw [show radialScale r ^ 4 = (radialScale r ^ 2) ^ 2 by ring,
      radialScale_sq hr, inv_pow]
  rw [euclidean_scalarCurvature_zero, zero_mul, add_zero,
    laplacian_cylinderLift hw hr x, cylinderLift_smul w hr x]
  simp only [radialProfile, zero_sub, mul_pow, hs4]
  field_simp [hr.ne']
  ring

def radialCylinder (v : ℝ → ℝ) (p : ℝ × S) : ℝ := v p.1

theorem smooth_radialCylinder {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (radialCylinder v) :=
  hv.contMDiff.comp contMDiff_fst

theorem native_yamabe_cylinder_firstVariation {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    {w : ℝ × S → ℝ} (hw : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ w)
    {r : ℝ} (hr : 0 < r) (x : S) :
    HasDerivAt (fun a : ℝ =>
      -8 * euclideanD.laplacian
        (fun y => cylinderLift (radialCylinder v) y + a * cylinderLift w y) (r • (x : E)) +
        euclideanD.scalarCurvature (r • (x : E)) *
          (cylinderLift (radialCylinder v) (r • (x : E)) + a * cylinderLift w (r • (x : E))) -
        6 * (cylinderLift (radialCylinder v) (r • (x : E)) + a * cylinderLift w (r • (x : E))) ^ 5)
      ((-8 * radialScale r / r ^ 2) *
        (deriv (deriv (fun t : ℝ => w (t, x))) (-Real.log r) +
          sphereD.laplacian (fun y : S => w (-Real.log r, y)) x - w (-Real.log r, x) / 4 +
          (15 / 4 : ℝ) * v (-Real.log r) ^ 4 * w (-Real.log r, x))) 0 := by
  have hbase : cylinderLift (radialCylinder v) (r • (x : E)) = radialProfile v 0 r := by
    rw [cylinderLift_smul (radialCylinder v) hr x]
    simp only [radialCylinder, radialProfile, zero_sub]
  have hnorm : ‖r • (x : E)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
  have hne : r • (x : E) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact hr.ne' hnorm.symm
  have h := native_yamabe_hasDerivAt euclideanD
    (contDiffAt_cylinderLift (smooth_radialCylinder hv) hne).contMDiffAt
    (contDiffAt_cylinderLift hw hne).contMDiffAt
  simpa only [hbase, native_yamabe_linearized_cylinder v hw hr x] using h

#print axioms native_yamabe_linearized_cylinder
#print axioms native_yamabe_cylinder_firstVariation

end Yamabe3.Analysis.SpherePolar
