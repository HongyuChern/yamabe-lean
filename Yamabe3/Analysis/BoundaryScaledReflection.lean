import Yamabe3.Analysis.BoundaryWeakFaceTests

/-! One reflected sample fixes tangential points and scales the inward
normal coordinate. All integral identities include the actual Jacobian. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.BoundaryTangential
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

def scaledReflect (r : ℝ) (hr : 0 < r) : E ≃L[ℝ] E :=
  normalScaling (-r) (neg_ne_zero.mpr hr.ne')

def reflectedSample (r : ℝ) (hr : 0 < r) (u : E → ℝ) : E → ℝ :=
  fun x => (halfSpace d).indicator u (scaledReflect r hr x)

theorem scaledReflect_normal (r : ℝ) (hr : 0 < r) (x : E) :
    scaledReflect r hr x 0 = -r * x 0 := by simp [scaledReflect, normalFactor]

theorem reflectedSample_zero_on_positive (r : ℝ) (hr : 0 < r) (u : E → ℝ)
    {x : E} (hx : x ∈ halfSpace d) : reflectedSample r hr u x = 0 := by
  apply indicator_of_notMem
  change ¬ 0 < scaledReflect r hr x 0
  rw [scaledReflect_normal]
  exact not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr.le) hx.le)

theorem memLp_reflectedSample (r : ℝ) (hr : 0 < r) {u : E → ℝ}
    (hu : MemLp u 2 (volume.restrict (halfSpace d))) :
    MemLp (reflectedSample r hr u) 2 volume := by
  have hi := (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hu
  have he : MeasurableEmbedding (scaledReflect (d := d) r hr) :=
    (scaledReflect r hr).toHomeomorph.measurableEmbedding
  change MemLp ((halfSpace d).indicator u ∘ scaledReflect r hr) 2 volume
  rw [← he.memLp_map_measure_iff]
  change MemLp ((halfSpace d).indicator u) 2 (Measure.map (normalScaling (-r) _) volume)
  rw [map_volume_normalScaling]
  exact hi.smul_measure ENNReal.ofReal_ne_top

theorem eLpNorm_reflectedSample_le (r : ℝ) (hr : 0 < r) {u : E → ℝ}
    (hu : MemLp u 2 (volume.restrict (halfSpace d))) :
    eLpNorm (reflectedSample r hr u) 2 volume ≤
      (ENNReal.ofReal r⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal *
        eLpNorm u 2 (volume.restrict (halfSpace d)) := by
  have hi := (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hu
  have he : MeasurableEmbedding (scaledReflect (d := d) r hr) :=
    (scaledReflect r hr).toHomeomorph.measurableEmbedding
  change eLpNorm ((halfSpace d).indicator u ∘ scaledReflect r hr) 2 volume ≤ _
  rw [← he.eLpNorm_map_measure]
  change eLpNorm ((halfSpace d).indicator u) 2 (Measure.map (normalScaling (-r) _) volume) ≤ _
  rw [map_volume_normalScaling, eLpNorm_smul_measure_of_ne_zero
    (ne_of_gt (ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero (neg_ne_zero.mpr hr.ne'))))),
    eLpNorm_indicator_eq_eLpNorm_restrict isOpen_halfSpace.measurableSet]
  simp only [inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hr)]
  exact le_rfl

theorem integral_reflectedSample (r : ℝ) (hr : 0 < r) (u φ : E → ℝ) :
    (∫ x, reflectedSample r hr u x * φ x) =
      r⁻¹ * ∫ x in halfSpace d, u x * φ ((scaledReflect r hr).symm x) := by
  have h := integral_normalScaling (-r) (neg_ne_zero.mpr hr.ne')
    (fun x => (halfSpace d).indicator u x * φ ((scaledReflect r hr).symm x))
  change (∫ x, (halfSpace d).indicator u (scaledReflect r hr x) *
    φ ((scaledReflect r hr).symm (scaledReflect r hr x))) = _ at h
  simp only [ContinuousLinearEquiv.symm_apply_apply, inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hr)] at h
  refine h.trans ?_
  congr 1
  rw [← integral_indicator isOpen_halfSpace.measurableSet]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ halfSpace d <;> simp [hx]

theorem reflected_test_partial_scaled (r : ℝ) (hr : 0 < r) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (i : Fin d) (x : E) :
    fderiv ℝ (fun y => φ ((scaledReflect r hr).symm y)) x (EuclideanSpace.single i 1) =
      normalFactor (-r)⁻¹ i * fderiv ℝ φ ((scaledReflect r hr).symm x) (EuclideanSpace.single i 1) := by
  have hd := ((hφ.differentiable (by simp) _).hasFDerivAt.comp x
    (scaledReflect r hr).symm.toContinuousLinearMap.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => φ ((scaledReflect r hr).symm y)) x = _ at hd
  rw [hd]
  have he : (scaledReflect (d := d) r hr).symm (EuclideanSpace.single i 1) =
      normalFactor (-r)⁻¹ i • EuclideanSpace.single i 1 := by
    have hh := normalScaling_single (-r)⁻¹ (inv_ne_zero (neg_ne_zero.mpr hr.ne')) i
    convert hh using 1
    ext j
    rfl
  change fderiv ℝ φ ((scaledReflect r hr).symm x)
    ((scaledReflect r hr).symm (EuclideanSpace.single i 1)) = _
  rw [he, map_smul]
  rfl

#print axioms integral_reflectedSample
#print axioms eLpNorm_reflectedSample_le
#print axioms reflected_test_partial_scaled
end Yamabe3.Analysis.UniformElliptic
