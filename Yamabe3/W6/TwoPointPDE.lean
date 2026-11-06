import Yamabe3.W6.TwoPointCoordinates
import Yamabe3.Analysis.FlatDelaunayPDE
import Yamabe3.Geometry.SphericalConformalTransport

/-!
# A genuine native Yamabe solution for two arbitrary prescribed points

The radial profile is the constant cylinder profile, with fourth power 1/3.
It solves the actual flat native PDE.  The constructed two-point stereographic
diffeomorphism and its proved metric identity transport it to the actual
restricted round metric.  No nonlinear existence assumption occurs here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set PoincareMT
open scoped Manifold ContDiff

namespace Yamabe3.W6

open Yamabe3.Geometry Yamabe3.Analysis.Delaunay

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S3" => RoundStereographicSphere 3

def cylinderAmplitude : ℝ := Real.sqrt (Real.sqrt (1 / 3 : ℝ))

theorem cylinderAmplitude_pos : 0 < cylinderAmplitude := by
  unfold cylinderAmplitude
  positivity

theorem cylinderAmplitude_pow_four : cylinderAmplitude ^ 4 = 1 / 3 := by
  unfold cylinderAmplitude
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
    Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num)]

theorem constantCylinderProfile_ode (t : ℝ) :
    deriv (deriv (fun _ : ℝ => cylinderAmplitude)) t =
      cylinderAmplitude / 4 - 3 * cylinderAmplitude ^ 5 / 4 := by
  have hp : cylinderAmplitude ^ 5 = cylinderAmplitude * (1 / 3) := by
    rw [show cylinderAmplitude ^ 5 = cylinderAmplitude * cylinderAmplitude ^ 4 by ring,
      cylinderAmplitude_pow_four]
  simp only [deriv_const', deriv_const, hp]
  ring

def euclideanCylinderFunction (x : euclideanPuncturedOpen) : ℝ :=
  radialProfile (fun _ => cylinderAmplitude) 0 ‖(x : E3)‖

theorem euclideanCylinderFunction_smooth :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ euclideanCylinderFunction :=
  flat_radialProfile_restricted_smooth euclideanPuncturedOpen
    (fun x => (mem_euclideanPuncturedOpen x.val).mp x.property) contDiff_const 0

theorem euclideanCylinderFunction_pos (x : euclideanPuncturedOpen) :
    0 < euclideanCylinderFunction x :=
  mul_pos (radialScale_pos _) cylinderAmplitude_pos

/-- The precise global lower bound used for metric completeness. -/
theorem euclideanCylinderFunction_sq (x : euclideanPuncturedOpen) :
    euclideanCylinderFunction x ^ 2 = cylinderAmplitude ^ 2 / ‖(x : E3)‖ := by
  have hx : 0 < ‖(x : E3)‖ := norm_pos_iff.mpr
    ((mem_euclideanPuncturedOpen x.val).mp x.property)
  rw [euclideanCylinderFunction, radialProfile, mul_pow, radialScale_sq hx]
  rw [div_eq_mul_inv]
  exact mul_comm _ _

theorem euclideanCylinderFunction_native_equation (x : euclideanPuncturedOpen) :
    let g := restrictMetric (RiemannianMetric.euclideanMetric 3) euclideanPuncturedOpen;
    -8 * g.leviCivitaData.laplacian euclideanCylinderFunction x +
      g.leviCivitaData.scalarCurvature x * euclideanCylinderFunction x =
      6 * euclideanCylinderFunction x ^ 5 :=
  flat_radialProfile_restricted_equation euclideanPuncturedOpen
    (fun y => (mem_euclideanPuncturedOpen y.val).mp y.property)
    contDiff_const constantCylinderProfile_ode 0 x

def twoPointConformalFactor (p q : S3) (x : twoPointOpen p q) : ℝ :=
  (roundStereographicFactor (pointChart p x.val))⁻¹

theorem twoPointConformalFactor_smooth (p q : S3) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (twoPointConformalFactor p q) := by
  have hchart : ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun x : twoPointOpen p q => pointChart p x.val) := by
    intro x
    exact contMDiffAt_subtype_iff.mpr (pointChart_contMDiffAt p x.val
      ((mem_twoPointOpen p q x.val).mp x.property).1)
  exact (roundStereographicFactor_contMDiff.comp hchart).inv₀
    (fun x => (roundStereographicFactor_pos _).ne')

theorem twoPointConformalFactor_pos (p q : S3) (x : twoPointOpen p q) :
    0 < twoPointConformalFactor p q x :=
  inv_pos.mpr (roundStereographicFactor_pos _)

/-- The function is explicitly the reciprocal stereographic factor times
the translated flat cylinder profile.  Both input punctures are retained. -/
def twoPointYamabeFunction (p q : S3) (hpq : p ≠ q)
    (x : twoPointOpen p q) : ℝ :=
  twoPointConformalFactor p q x *
    euclideanCylinderFunction (twoPointDiffeomorph p q hpq x)

theorem twoPointYamabeFunction_smooth (p q : S3) (hpq : p ≠ q) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (twoPointYamabeFunction p q hpq) :=
  (twoPointConformalFactor_smooth p q).mul
    (euclideanCylinderFunction_smooth.comp (twoPointDiffeomorph p q hpq).contMDiff)

theorem twoPointYamabeFunction_pos (p q : S3) (hpq : p ≠ q)
    (x : twoPointOpen p q) : 0 < twoPointYamabeFunction p q hpq x :=
  mul_pos (twoPointConformalFactor_pos p q x) (euclideanCylinderFunction_pos _)

/-- An unconditional exact equation for the actual round-sphere native
Laplacian and scalar curvature, for every pair of distinct prescribed points. -/
theorem twoPointYamabeFunction_native_equation (p q : S3) (hpq : p ≠ q)
    (x : twoPointOpen p q) :
    let g := restrictMetric PoincareMT.M38.threeSphereMetric (twoPointOpen p q);
    -8 * g.leviCivitaData.laplacian (twoPointYamabeFunction p q hpq) x +
      g.leviCivitaData.scalarCurvature x * twoPointYamabeFunction p q hpq x =
      6 * twoPointYamabeFunction p q hpq x ^ 5 := by
  exact (yamabe_equation_conformal_diffeomorph_iff
    (restrictMetric PoincareMT.M38.threeSphereMetric (twoPointOpen p q))
    (restrictMetric (RiemannianMetric.euclideanMetric 3) euclideanPuncturedOpen)
    (twoPointDiffeomorph p q hpq) (twoPointConformalFactor p q)
    euclideanCylinderFunction (twoPointConformalFactor_smooth p q)
    euclideanCylinderFunction_smooth (twoPointConformalFactor_pos p q)
    euclideanCylinderFunction_pos (twoPoint_forward_metric p q hpq) x).mp
      (euclideanCylinderFunction_native_equation (twoPointDiffeomorph p q hpq x))

theorem twoPointYamabeFunction_sq (p q : S3) (hpq : p ≠ q)
    (x : twoPointOpen p q) :
    twoPointYamabeFunction p q hpq x ^ 2 =
      (roundStereographicFactor (pointChart p x.val))⁻¹ ^ 2 *
        (cylinderAmplitude ^ 2 / ‖pointChart p x.val - pointChart p q‖) := by
  rw [twoPointYamabeFunction, mul_pow, euclideanCylinderFunction_sq]
  rfl

/-- This packages the function already constructed above, without a free
existence field or a source-PDE assumption.  Completeness is proved separately. -/
theorem exists_twoPoint_native_solution (p q : S3) (hpq : p ≠ q) :
    ∃ u : twoPointOpen p q → ℝ,
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u ∧ (∀ x, 0 < u x) ∧
      ∀ x, let g := restrictMetric PoincareMT.M38.threeSphereMetric (twoPointOpen p q);
        -8 * g.leviCivitaData.laplacian u x + g.leviCivitaData.scalarCurvature x * u x =
          6 * u x ^ 5 :=
  ⟨twoPointYamabeFunction p q hpq, twoPointYamabeFunction_smooth p q hpq,
    twoPointYamabeFunction_pos p q hpq, twoPointYamabeFunction_native_equation p q hpq⟩

#print axioms twoPointYamabeFunction_native_equation
#print axioms exists_twoPoint_native_solution

end Yamabe3.W6
