import Yamabe3.Analysis.Cylinder.NativeCylinderLift
import Mathlib.Topology.Algebra.Support

/-!
# Genuine compact test functions under cylinder coordinates

The actual punctured Euclidean space is homeomorphic to the real cylinder.
A compactly supported smooth cylinder function has a globally smooth
compact Euclidean lift, whose closed support excludes the origin.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareMT
open scoped Manifold ContDiff Bundle Topology

namespace Yamabe3.Analysis.SpherePolar

open Poincare.Geometry.Riemannian.SpaceForm

def cylinderPoint (p : ℝ × S) : E := Real.exp (-p.1) • (p.2 : E)

theorem cylinderPoint_norm (p : ℝ × S) : ‖cylinderPoint p‖ = Real.exp (-p.1) := by
  simp only [cylinderPoint, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    norm_eq_of_mem_sphere, mul_one]

theorem cylinderPoint_ne_zero (p : ℝ × S) : cylinderPoint p ≠ 0 := by
  intro h
  have hn := cylinderPoint_norm p
  rw [h, norm_zero] at hn
  exact (Real.exp_pos (-p.1)).ne' hn.symm

def puncturedCylinderPoint (p : ℝ × S) : puncturedSpace :=
  ⟨cylinderPoint p, by change cylinderPoint p ≠ 0; exact cylinderPoint_ne_zero p⟩

theorem continuous_cylinderPoint : Continuous cylinderPoint :=
  (Real.continuous_exp.comp continuous_fst.neg).smul
    (continuous_subtype_val.comp continuous_snd)

theorem cylinderCoordinates_point (p : ℝ × S) :
    cylinderCoordinates (puncturedCylinderPoint p) = p := by
  apply Prod.ext
  · change -Real.log ‖cylinderPoint p‖ = p.1
    rw [cylinderPoint_norm, Real.log_exp, neg_neg]
  · apply Subtype.ext
    change ‖cylinderPoint p‖⁻¹ • cylinderPoint p = (p.2 : E)
    rw [cylinderPoint_norm]
    change (Real.exp (-p.1))⁻¹ • (Real.exp (-p.1) • (p.2 : E)) = _
    rw [smul_smul, inv_mul_cancel₀ (Real.exp_ne_zero _), one_smul]

theorem cylinderPoint_coordinates (x : puncturedSpace) :
    cylinderPoint (cylinderCoordinates x) = (x : E) := by
  change Real.exp (-(-Real.log ‖(x : E)‖)) • (sphereDirection x : E) = (x : E)
  rw [neg_neg, Real.exp_log (norm_pos_iff.mpr (punctured_ne_zero x)),
    norm_smul_sphereDirection]

def cylinderHomeomorph : puncturedSpace ≃ₜ (ℝ × S) where
  toFun := cylinderCoordinates
  invFun := puncturedCylinderPoint
  left_inv x := Subtype.ext (cylinderPoint_coordinates x)
  right_inv := cylinderCoordinates_point
  continuous_toFun := smooth_cylinderCoordinates.continuous
  continuous_invFun := continuous_cylinderPoint.subtype_mk _

theorem hasCompactSupport_puncturedCylinderLift {v : ℝ × S → ℝ}
    (hv : HasCompactSupport v) : HasCompactSupport (puncturedCylinderLift v) := by
  have h := hv.comp_isClosedEmbedding cylinderHomeomorph.isClosedEmbedding
  exact h.mul_left

theorem hasCompactSupport_cylinderLift {v : ℝ × S → ℝ}
    (hv : HasCompactSupport v) : HasCompactSupport (cylinderLift v) :=
  (hasCompactSupport_puncturedCylinderLift hv).extend_zero continuous_subtype_val

theorem zero_notMem_tsupport_cylinderLift {v : ℝ × S → ℝ}
    (hv : HasCompactSupport v) : (0 : E) ∉ tsupport (cylinderLift v) := by
  intro h
  have hi := (hasCompactSupport_puncturedCylinderLift hv).tsupport_extend_zero_subset
    (g := (Subtype.val : puncturedSpace → E)) continuous_subtype_val h
  obtain ⟨x, _, hx⟩ := hi
  exact punctured_ne_zero x hx

theorem contDiff_cylinderLift_of_compact {v : ℝ × S → ℝ}
    (hv : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ v)
    (hc : HasCompactSupport v) : ContDiff ℝ ∞ (cylinderLift v) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp (zero_notMem_tsupport_cylinderLift hc))
  · exact contDiffAt_cylinderLift hv hx

#print axioms cylinderHomeomorph
#print axioms contDiff_cylinderLift_of_compact
#print axioms zero_notMem_tsupport_cylinderLift

end Yamabe3.Analysis.SpherePolar
