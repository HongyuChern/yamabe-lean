import Yamabe3.Analysis.Cylinder.NativeCylinderJacobi
import Yamabe3.Analysis.Sphere.NativeSphereHighModes
import Yamabe3.Analysis.DelaunayJacobi

/-!
# The scalar Jacobi modes are actual native Euclidean Yamabe modes

This connects the scalar operator used by the Delaunay inverse modules to
the true Euclidean linearization and the actual induced-sphere Laplacian.
The final existence statement chooses the angular eigenfunction from the
constructed native Hilbert basis, rather than taking an angular spectrum
as an unproved premise.
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
open Yamabe3.Analysis.SphereSpectrum

def separableCylinder (q : ℝ → ℝ) (φ : S → ℝ) (p : ℝ × S) : ℝ :=
  q p.1 * φ p.2

theorem smooth_separableCylinder {q : ℝ → ℝ} {φ : S → ℝ}
    (hq : ContDiff ℝ ∞ q) (hφ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ φ) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (separableCylinder q φ) :=
  (hq.contMDiff.comp contMDiff_fst).mul (hφ.comp contMDiff_snd)

theorem native_yamabe_linearized_eigenmode (v : ℝ → ℝ) {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) {φ : S → ℝ}
    (hφ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ φ) {μ : ℝ}
    (heigen : ∀ x, -sphereD.laplacian φ x = μ * φ x)
    {r : ℝ} (hr : 0 < r) (x : S) :
    -8 * euclideanD.laplacian (cylinderLift (separableCylinder q φ)) (r • (x : E)) +
      euclideanD.scalarCurvature (r • (x : E)) *
        cylinderLift (separableCylinder q φ) (r • (x : E)) -
      30 * radialProfile v 0 r ^ 4 * cylinderLift (separableCylinder q φ) (r • (x : E)) =
      (-8 * radialScale r / r ^ 2) * modelJacobi v μ q (-Real.log r) * φ x := by
  have hs4 : radialScale r ^ 4 = (r ^ 2)⁻¹ := by
    rw [show radialScale r ^ 4 = (radialScale r ^ 2) ^ 2 by ring,
      radialScale_sq hr, inv_pow]
  have hΔ : sphereD.laplacian φ x = -μ * φ x := by linarith [heigen x]
  rw [euclidean_scalarCurvature_zero, zero_mul, add_zero,
    laplacian_cylinderLift (smooth_separableCylinder hq hφ) hr x,
    cylinderLift_smul (separableCylinder q φ) hr x]
  simp only [separableCylinder, deriv_mul_const_field', sphereD.laplacian_const_mul,
    radialProfile, zero_sub, mul_pow, hs4, hΔ, modelJacobi]
  field_simp [hr.ne']
  ring

theorem exists_native_angular_eigenmode_linearization (i : AngularIndex) :
    ∃ φ : S → ℝ,
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ φ ∧
      φ =ᵐ[(roundSphereMetric 2).volumeMeasure] (angularBasis i : S → ℝ) ∧
      (∃ x, φ x ≠ 0) ∧
      ∀ (v q : ℝ → ℝ), ContDiff ℝ ∞ q → ∀ r : ℝ, 0 < r → ∀ x : S,
        -8 * euclideanD.laplacian (cylinderLift (separableCylinder q φ)) (r • (x : E)) +
          euclideanD.scalarCurvature (r • (x : E)) *
            cylinderLift (separableCylinder q φ) (r • (x : E)) -
          30 * radialProfile v 0 r ^ 4 * cylinderLift (separableCylinder q φ) (r • (x : E)) =
          (-8 * radialScale r / r ^ 2) * modelJacobi v (angularEigenvalue i) q (-Real.log r) * φ x := by
  obtain ⟨φ, hφ, hae, hne, he⟩ := exists_smooth_angular_eigenfunction i
  exact ⟨φ, hφ, hae, hne, fun v q hq r hr x => native_yamabe_linearized_eigenmode v hq hφ he hr x⟩

#print axioms native_yamabe_linearized_eigenmode
#print axioms exists_native_angular_eigenmode_linearization

end Yamabe3.Analysis.SpherePolar
