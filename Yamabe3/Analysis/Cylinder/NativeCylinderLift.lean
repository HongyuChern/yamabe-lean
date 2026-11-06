import Yamabe3.Analysis.Cylinder.NativeSphereRestriction
import Yamabe3.Analysis.DelaunayRadialProfile
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# The actual smooth Euclidean lift of a cylinder function

The direction map is constructed on the genuine punctured Euclidean open
submanifold and proved smooth by the ordinary norm and sphere restriction
rules.  Extension by zero only totalizes the missing origin.  Away from
that origin the actual Euclidean function is smooth and equals the desired
r^(-1/2) times the cylinder function at (-log r, omega).
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open Poincare.Geometry.Riemannian.SpaceForm
open Yamabe3.Analysis.Delaunay

def puncturedSpace : TopologicalSpace.Opens E :=
  ⟨({(0 : E)} : Set E)ᶜ, isClosed_singleton.isOpen_compl⟩

theorem punctured_ne_zero (x : puncturedSpace) : (x : E) ≠ 0 := by
  have hx := x.property
  change (x : E) ≠ 0 at hx
  exact hx

local instance sphereDimensionCylinder : Fact (Module.finrank ℝ E = 2 + 1) :=
  ⟨by simp [E]⟩

def sphereDirection (x : puncturedSpace) : S :=
  ⟨‖(x : E)‖⁻¹ • (x : E), by
    have hn : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.mpr (punctured_ne_zero x)
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg (x : E))), inv_mul_cancel₀ hn]⟩

theorem norm_smul_sphereDirection (x : puncturedSpace) :
    ‖(x : E)‖ • (sphereDirection x : E) = (x : E) := by
  change ‖(x : E)‖ • (‖(x : E)‖⁻¹ • (x : E)) = (x : E)
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (punctured_ne_zero x)), one_smul]

theorem smooth_punctured_norm :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x : puncturedSpace => ‖(x : E)‖) := by
  intro x
  exact (contDiffAt_norm ℝ (punctured_ne_zero x)).contMDiffAt.comp x
    (contMDiff_subtype_val x)

theorem smooth_sphereDirection : ContMDiff (𝓡 3) (𝓡 2) ∞ sphereDirection := by
  have hs : ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun x : puncturedSpace => ‖(x : E)‖⁻¹ • (x : E)) :=
    (smooth_punctured_norm.inv₀ (fun x => norm_ne_zero_iff.mpr (punctured_ne_zero x))).smul
      contMDiff_subtype_val
  exact hs.codRestrict_sphere (fun x => (sphereDirection x).property)

def cylinderCoordinates (x : puncturedSpace) : ℝ × S :=
  (-Real.log ‖(x : E)‖, sphereDirection x)

theorem smooth_cylinderCoordinates :
    ContMDiff (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ cylinderCoordinates := by
  have ht : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun x : puncturedSpace => -Real.log ‖(x : E)‖) := by
    intro x
    have hl : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => -Real.log s) ‖(x : E)‖ :=
      ((Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr (punctured_ne_zero x))).neg).contMDiffAt
    exact hl.comp (f := fun y : puncturedSpace => ‖(y : E)‖)
      (g := fun s : ℝ => -Real.log s) x (smooth_punctured_norm x)
  exact ht.prodMk smooth_sphereDirection

def puncturedCylinderLift (v : ℝ × S → ℝ) (x : puncturedSpace) : ℝ :=
  radialScale ‖(x : E)‖ * v (cylinderCoordinates x)

def cylinderLift (v : ℝ × S → ℝ) : E → ℝ :=
  (Subtype.val : puncturedSpace → E).extend (puncturedCylinderLift v) 0

theorem cylinderLift_coe (v : ℝ × S → ℝ) (x : puncturedSpace) :
    cylinderLift v (x : E) = puncturedCylinderLift v x :=
  Subtype.val_injective.extend_apply _ _ x

theorem smooth_puncturedCylinderLift {v : ℝ × S → ℝ}
    (hv : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ v) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (puncturedCylinderLift v) := by
  have hs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun x : puncturedSpace => radialScale ‖(x : E)‖) := by
    intro x
    have hl : ContDiffAt ℝ ∞ Real.log ‖(x : E)‖ :=
      Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr (punctured_ne_zero x))
    have hs : ContDiffAt ℝ ∞ radialScale ‖(x : E)‖ := (hl.neg.div_const 2).exp
    exact hs.contMDiffAt.comp (f := fun y : puncturedSpace => ‖(y : E)‖)
      (g := radialScale) x (smooth_punctured_norm x)
  exact hs.mul (hv.comp smooth_cylinderCoordinates)

theorem contDiffAt_cylinderLift {v : ℝ × S → ℝ}
    (hv : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ v)
    {x : E} (hx : x ≠ 0) : ContDiffAt ℝ ∞ (cylinderLift v) x := by
  let y : puncturedSpace := ⟨x, by change x ≠ 0; exact hx⟩
  have h : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun z : puncturedSpace => cylinderLift v (z : E)) y := by
    simpa only [cylinderLift_coe] using smooth_puncturedCylinderLift hv y
  exact contMDiffAt_iff_contDiffAt.mp (contMDiffAt_subtype_iff.mp h)

theorem cylinderLift_smul (v : ℝ × S → ℝ) {r : ℝ} (hr : 0 < r) (x : S) :
    cylinderLift v (r • (x : E)) = radialScale r * v (-Real.log r, x) := by
  have hnorm : ‖r • (x : E)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
  have hne : r • (x : E) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact hr.ne' hnorm.symm
  let y : puncturedSpace :=
    ⟨r • (x : E), by change r • (x : E) ≠ 0; exact hne⟩
  have hd : sphereDirection y = x := by
    apply Subtype.ext
    change ‖r • (x : E)‖⁻¹ • (r • (x : E)) = (x : E)
    rw [hnorm, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  change cylinderLift v (y : E) = _
  rw [cylinderLift_coe]
  change radialScale ‖r • (x : E)‖ * v (-Real.log ‖r • (x : E)‖, sphereDirection y) = _
  rw [hnorm, hd]

theorem smooth_cylinder_time_slice {v : ℝ × S → ℝ}
    (hv : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ v) (x : S) :
    ContDiff ℝ ∞ (fun t : ℝ => v (t, x)) := by
  exact contMDiff_iff_contDiff.mp (hv.comp (contMDiff_id.prodMk contMDiff_const))

theorem smooth_cylinder_sphere_slice {v : ℝ × S → ℝ}
    (hv : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ v) (t : ℝ) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x : S => v (t, x)) :=
  hv.comp (contMDiff_const.prodMk contMDiff_id)

#print axioms contDiffAt_cylinderLift
#print axioms cylinderLift_smul

end Yamabe3.Analysis.SpherePolar
