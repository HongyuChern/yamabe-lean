import Yamabe3.Analysis.Cylinder.NativeLogPolarIntegrals
import Yamabe3.Analysis.Cylinder.NativeCylinderPullback
import Yamabe3.Analysis.Cylinder.NativeCylinderJacobi
import PoincareLib.Geometry.Riemannian.ScalarOperators.Divergence.Regularity

/-!
# Actual transposed cylinder-to-Euclidean Jacobi transport

The r³ volume Jacobian cancels the actual r^(-1/2) solution lift and
r^(-5/2) test-operator factor. Both integrability and the integral identity
are transferred. This module transports a proved cylinder weak equation;
it does not postulate a geometric inverse or identify different weights.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology

namespace Yamabe3.Analysis.SpherePolar

open Yamabe3.Analysis.Delaunay

/-- The actual induced-sphere operator applied to a genuine joint test. -/
def cylinderJacobiTest (v : ℝ → ℝ) (η : ℝ × S → ℝ) (p : ℝ × S) : ℝ :=
  deriv (deriv (fun t : ℝ => η (t, p.2))) p.1 +
    sphereD.laplacian (fun θ : S => η (p.1, θ)) p.2 - η p / 4 +
      (15 / 4) * v p.1 ^ 4 * η p

/-- The actual Euclidean linearization at the lifted radial profile. -/
def physicalJacobi (v : ℝ → ℝ) (φ : E → ℝ) (x : E) : ℝ :=
  -8 * euclideanD.laplacian φ x + euclideanD.scalarCurvature x * φ x -
    30 * cylinderLift (radialCylinder v) x ^ 4 * φ x

/-- Actual physical forcing associated to cylinder forcing. -/
def physicalForcing (f : ℝ × S → ℝ) (x : E) : ℝ :=
  -8 * cylinderLift f x / ‖x‖ ^ 2

theorem physicalJacobi_lift {η : ℝ × S → ℝ}
    (hη : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ η)
    (v : ℝ → ℝ) {r : ℝ} (hr : 0 < r) (θ : S) :
    physicalJacobi v (cylinderLift η) (r • (θ : E)) =
      (-8 * radialScale r / r ^ 2) * cylinderJacobiTest v η (-Real.log r, θ) := by
  have hb : cylinderLift (radialCylinder v) (r • (θ : E)) = radialProfile v 0 r := by
    rw [cylinderLift_smul _ hr]
    simp only [radialCylinder, radialProfile, zero_sub]
  simpa only [physicalJacobi, hb, cylinderJacobiTest] using
    native_yamabe_linearized_cylinder v hη hr θ

theorem logarithmic_pairing_factor (t a b : ℝ) :
    Real.exp (-3 * t) * (radialScale (Real.exp (-t)) * a) *
      ((-8 * radialScale (Real.exp (-t)) / Real.exp (-t) ^ 2) * b) = -8 * a * b := by
  let r := Real.exp (-t)
  have hr : 0 < r := Real.exp_pos _
  have hj : Real.exp (-3 * t) = r ^ 3 := by
    rw [← exp_polar_jacobian]
    dsimp [r]
    ring
  have hs : r * radialScale r ^ 2 = 1 := by
    rw [radialScale_sq hr, mul_inv_cancel₀ hr.ne']
  rw [hj]
  change r ^ 3 * (radialScale r * a) * ((-8 * radialScale r / r ^ 2) * b) = _
  calc
    _ = -8 * (r * radialScale r ^ 2) * a * b := by field_simp [hr.ne'] <;> ring
    _ = _ := by rw [hs]; ring

theorem logCylinderWeight_jacobi_pairing (v : ℝ → ℝ) (w : ℝ × S → ℝ)
    {η : ℝ × S → ℝ}
    (hη : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ η) :
    logCylinderWeight (fun x : E => cylinderLift w x * physicalJacobi v (cylinderLift η) x) =
      fun p : ℝ × S => -8 * (w p * cylinderJacobiTest v η p) := by
  funext p
  change Real.exp (-3 * p.1) *
    (cylinderLift w (Real.exp (-p.1) • (p.2 : E)) *
      physicalJacobi v (cylinderLift η) (Real.exp (-p.1) • (p.2 : E))) = _
  rw [physicalJacobi_lift hη v (Real.exp_pos _) p.2,
    cylinderLift_smul w (Real.exp_pos _) p.2, Real.log_exp, neg_neg]
  rw [← mul_assoc, logarithmic_pairing_factor]
  ring

theorem logCylinderWeight_forcing_pairing (f η : ℝ × S → ℝ) :
    logCylinderWeight (fun x : E => physicalForcing f x * cylinderLift η x) =
      fun p : ℝ × S => -8 * (f p * η p) := by
  funext p
  have hn : ‖Real.exp (-p.1) • (p.2 : E)‖ = Real.exp (-p.1) :=
    cylinderPoint_norm p
  change Real.exp (-3 * p.1) *
    ((-8 * cylinderLift f (Real.exp (-p.1) • (p.2 : E)) /
      ‖Real.exp (-p.1) • (p.2 : E)‖ ^ 2) *
      cylinderLift η (Real.exp (-p.1) • (p.2 : E))) = _
  rw [cylinderLift_smul f (Real.exp_pos _) p.2,
    cylinderLift_smul η (Real.exp_pos _) p.2, hn, Real.log_exp, neg_neg]
  calc
    _ = Real.exp (-3 * p.1) * (radialScale (Real.exp (-p.1)) * f p) *
        ((-8 * radialScale (Real.exp (-p.1)) / Real.exp (-p.1) ^ 2) * η p) := by ring
    _ = _ := by rw [logarithmic_pairing_factor]; ring

theorem measurable_physicalForcing {f : ℝ × S → ℝ} (hf : Measurable f) :
    Measurable (physicalForcing f) :=
  (measurable_const.mul (measurable_cylinderLift hf)).div (measurable_norm.pow_const 2)

theorem measurable_physicalJacobi {v : ℝ → ℝ} (hv : Measurable v)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) : Measurable (physicalJacobi v φ) := by
  have hV : Measurable (cylinderLift (radialCylinder v)) :=
    measurable_cylinderLift (hv.comp measurable_fst)
  have hΔ : Measurable (euclideanD.laplacian φ) :=
    (euclideanD.contMDiff_laplacian hφ.contMDiff).continuous.measurable
  have hφm := hφ.continuous.measurable
  have hR : Measurable euclideanD.scalarCurvature := by
    have he : euclideanD.scalarCurvature = fun _ : E => (0 : ℝ) :=
      funext euclidean_scalarCurvature_zero
    rw [he]
    exact measurable_const
  exact ((measurable_const.mul hΔ).add (hR.mul hφm)).sub
    ((measurable_const.mul (hV.pow_const 4)).mul hφm)

/-- Every integrable joint cylinder test pairing is a legitimate physical
pairing against the actual native Euclidean Jacobi operator. -/
theorem integral_physical_jacobi_pairing {v : ℝ → ℝ} (hv : Measurable v)
    {w : ℝ × S → ℝ} (hw : Measurable w) {η : ℝ × S → ℝ}
    (hη : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ η)
    (hc : HasCompactSupport η)
    (hi : Integrable (fun p => w p * cylinderJacobiTest v η p) (volume.prod angularVolume)) :
    Integrable (fun x : E => cylinderLift w x * physicalJacobi v (cylinderLift η) x) ∧
      (∫ x : E, cylinderLift w x * physicalJacobi v (cylinderLift η) x) =
        -8 * ∫ t : ℝ, ∫ θ : S, w (t, θ) * cylinderJacobiTest v η (t, θ) ∂angularVolume := by
  have hm : Measurable (fun x : E => cylinderLift w x * physicalJacobi v (cylinderLift η) x) :=
    (measurable_cylinderLift hw).mul
    (measurable_physicalJacobi hv (contDiff_cylinderLift_of_compact hη hc))
  have hi' : Integrable (logCylinderWeight
      (fun x : E => cylinderLift w x * physicalJacobi v (cylinderLift η) x))
      (volume.prod angularVolume) := by
    rw [logCylinderWeight_jacobi_pairing v w hη]
    exact hi.const_mul (-8)
  refine ⟨(integrable_euclidean_iff_cylinder hm).mpr hi', ?_⟩
  rw [integral_euclidean_eq_cylinder_of_pullback hm hi']
  simp_rw [logCylinderWeight_jacobi_pairing v w hη, integral_const_mul]

theorem integral_physical_forcing_pairing {f : ℝ × S → ℝ} (hf : Measurable f)
    {η : ℝ × S → ℝ} (hη : Measurable η)
    (hi : Integrable (fun p => f p * η p) (volume.prod angularVolume)) :
    Integrable (fun x : E => physicalForcing f x * cylinderLift η x) ∧
      (∫ x : E, physicalForcing f x * cylinderLift η x) =
        -8 * ∫ t : ℝ, ∫ θ : S, f (t, θ) * η (t, θ) ∂angularVolume := by
  have hm : Measurable (fun x : E => physicalForcing f x * cylinderLift η x) :=
    (measurable_physicalForcing hf).mul (measurable_cylinderLift hη)
  have hi' : Integrable (logCylinderWeight
      (fun x : E => physicalForcing f x * cylinderLift η x))
      (volume.prod angularVolume) := by
    rw [logCylinderWeight_forcing_pairing]
    exact hi.const_mul (-8)
  refine ⟨(integrable_euclidean_iff_cylinder hm).mpr hi', ?_⟩
  rw [integral_euclidean_eq_cylinder_of_pullback hm hi']
  simp_rw [logCylinderWeight_forcing_pairing, integral_const_mul]

/-- An arbitrary joint cylinder weak equation transports to every genuine
compact smooth Euclidean test supported away from the missing origin.
The reverse test construction ensures that the conclusion is not confined
to separated tests or to a postulated polar test class. -/
theorem transport_native_cylinder_weak_equation
    {v : ℝ → ℝ} (hv : Measurable v)
    {w f : ℝ × S → ℝ} (hw : Measurable w) (hf : Measurable f)
    (hweak : ∀ η : ℝ × S → ℝ,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ η → HasCompactSupport η →
      Integrable (fun p => w p * cylinderJacobiTest v η p) (volume.prod angularVolume) ∧
      Integrable (fun p => f p * η p) (volume.prod angularVolume) ∧
      (∫ t : ℝ, ∫ θ : S, w (t, θ) * cylinderJacobiTest v η (t, θ) ∂angularVolume) =
        ∫ t : ℝ, ∫ θ : S, f (t, θ) * η (t, θ) ∂angularVolume) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (0 : E) ∉ tsupport φ →
      Integrable (fun x : E => cylinderLift w x * physicalJacobi v φ x) ∧
      Integrable (fun x : E => physicalForcing f x * φ x) ∧
      (∫ x : E, cylinderLift w x * physicalJacobi v φ x) =
        ∫ x : E, physicalForcing f x * φ x := by
  intro φ hφ hc hzero
  obtain ⟨η, hη, hηc, he⟩ := exists_compact_smooth_cylinder_test hφ hc hzero
  obtain ⟨hiJ, hiF, hEq⟩ := hweak η hη hηc
  have hJ := integral_physical_jacobi_pairing hv hw hη hηc hiJ
  have hF := integral_physical_forcing_pairing hf hη.continuous.measurable hiF
  rw [he] at hJ hF
  exact ⟨hJ.1, hF.1, hJ.2.trans ((congrArg (fun z : ℝ => -8 * z) hEq).trans hF.2.symm)⟩

#print axioms physicalJacobi_lift
#print axioms integral_physical_jacobi_pairing
#print axioms integral_physical_forcing_pairing
#print axioms transport_native_cylinder_weak_equation

end Yamabe3.Analysis.SpherePolar
