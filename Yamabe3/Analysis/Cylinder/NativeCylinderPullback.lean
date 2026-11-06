import Yamabe3.Analysis.Cylinder.NativeCylinderTest
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Actual inverse test pullback and measurable Euclidean lift

Every compact smooth Euclidean test whose closed support avoids zero is
the lift of an explicitly constructed compact smooth cylinder test.
Measurable cylinder functions also have genuinely measurable Euclidean
lifts, using the actual open-submanifold inclusion and extension.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology

namespace Yamabe3.Analysis.SpherePolar

open Poincare.Geometry.Riemannian.SpaceForm
open Yamabe3.Analysis.Delaunay

local instance sphereDimensionPullback : Fact (Module.finrank ℝ E = 2 + 1) :=
  ⟨by simp [E]⟩

theorem smooth_cylinderPoint :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ cylinderPoint :=
  (Real.contDiff_exp.contMDiff.comp contMDiff_fst.neg).smul
    (contMDiff_coe_sphere.comp contMDiff_snd)

theorem radialScale_exp_neg (t : ℝ) : radialScale (Real.exp (-t)) = Real.exp (t / 2) := by
  rw [radialScale, Real.log_exp, neg_neg]

def testPullback (φ : E → ℝ) (p : ℝ × S) : ℝ :=
  Real.exp (-p.1 / 2) * φ (cylinderPoint p)

theorem smooth_testPullback {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (testPullback φ) :=
  (Real.contDiff_exp.contMDiff.comp (contMDiff_fst.neg.div_const 2)).mul
    (hφ.contMDiff.comp smooth_cylinderPoint)

theorem hasCompactSupport_restrict_punctured {φ : E → ℝ}
    (hφ : HasCompactSupport φ) (hzero : (0 : E) ∉ tsupport φ) :
    HasCompactSupport (fun x : puncturedSpace => φ (x : E)) := by
  have hsubset : tsupport φ ⊆ Set.range (Subtype.val : puncturedSpace → E) := by
    intro x hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    change x ≠ 0
    rintro rfl
    exact hzero hx
  have hk := Topology.IsInducing.subtypeVal.isCompact_preimage' hφ.isCompact hsubset
  exact HasCompactSupport.of_support_subset_isCompact hk
    (fun x hx => subset_tsupport φ hx)

theorem hasCompactSupport_testPullback {φ : E → ℝ}
    (hφ : HasCompactSupport φ) (hzero : (0 : E) ∉ tsupport φ) :
    HasCompactSupport (testPullback φ) := by
  have h := (hasCompactSupport_restrict_punctured hφ hzero).comp_isClosedEmbedding
    cylinderHomeomorph.symm.isClosedEmbedding
  exact h.mul_left

theorem cylinderLift_zero (v : ℝ × S → ℝ) : cylinderLift v (0 : E) = 0 := by
  apply Function.extend_apply'
  rintro ⟨x, hx⟩
  exact punctured_ne_zero x hx

theorem testPullback_cylinderLift (v : ℝ × S → ℝ) : testPullback (cylinderLift v) = v := by
  funext p
  change Real.exp (-p.1 / 2) * cylinderLift v (Real.exp (-p.1) • (p.2 : E)) = v p
  rw [cylinderLift_smul v (Real.exp_pos _) p.2, radialScale_exp_neg, Real.log_exp, neg_neg,
    ← mul_assoc, ← Real.exp_add]
  simp only [show -p.1 / 2 + p.1 / 2 = 0 by ring, Real.exp_zero, one_mul]

theorem cylinderLift_testPullback {φ : E → ℝ} (hzero : φ 0 = 0) :
    cylinderLift (testPullback φ) = φ := by
  funext x
  by_cases hx : x = 0
  · subst x
    rw [cylinderLift_zero, hzero]
  · let y : puncturedSpace := ⟨x, by change x ≠ 0; exact hx⟩
    let p := cylinderCoordinates y
    have hp : cylinderPoint p = x := cylinderPoint_coordinates y
    rw [← hp]
    change cylinderLift (testPullback φ) (Real.exp (-p.1) • (p.2 : E)) = φ (cylinderPoint p)
    rw [cylinderLift_smul (testPullback φ) (Real.exp_pos _) p.2,
      radialScale_exp_neg, Real.log_exp, neg_neg]
    change Real.exp (p.1 / 2) * (Real.exp (-p.1 / 2) * φ (cylinderPoint p)) = _
    rw [← mul_assoc, ← Real.exp_add, show p.1 / 2 + -p.1 / 2 = 0 by ring,
      Real.exp_zero, one_mul]

theorem exists_compact_smooth_cylinder_test {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hzero : (0 : E) ∉ tsupport φ) :
    ∃ η : ℝ × S → ℝ,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ η ∧
      HasCompactSupport η ∧ cylinderLift η = φ :=
  ⟨testPullback φ, smooth_testPullback hφ, hasCompactSupport_testPullback hc hzero,
    cylinderLift_testPullback (image_eq_zero_of_notMem_tsupport hzero)⟩

theorem measurable_cylinderLift {v : ℝ × S → ℝ} (hv : Measurable v) :
    Measurable (cylinderLift v) := by
  have hs : Measurable (fun x : puncturedSpace => radialScale ‖(x : E)‖) := by
    unfold radialScale
    fun_prop
  exact (MeasurableEmbedding.subtype_coe isClosed_singleton.measurableSet.compl).measurable_extend
    (hs.mul (hv.comp smooth_cylinderCoordinates.continuous.measurable)) measurable_const

#print axioms exists_compact_smooth_cylinder_test
#print axioms measurable_cylinderLift

end Yamabe3.Analysis.SpherePolar
