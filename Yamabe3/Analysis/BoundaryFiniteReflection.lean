import Yamabe3.Analysis.BoundaryScaledReflection

/-! A finite normal reflection is an actual linear function construction.
Its restriction, L2 membership, norm and test integral are proved before
using any boundary moment conditions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.BoundaryTangential
variable {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ (Fin d)

def finiteReflection (r : ι → ℝ) (hr : ∀ j, 0 < r j) (c : ι → ℝ)
    (u : E → ℝ) (x : E) : ℝ :=
  (halfSpace d).indicator u x + ∑ j, c j * reflectedSample (r j) (hr j) u x

theorem finiteReflection_eq_on_halfSpace (r : ι → ℝ) (hr : ∀ j, 0 < r j)
    (c : ι → ℝ) (u : E → ℝ) : EqOn (finiteReflection r hr c u) u (halfSpace d) := by
  intro x hx
  simp only [finiteReflection, indicator_of_mem hx, reflectedSample_zero_on_positive _ _ _ hx,
    mul_zero, Finset.sum_const_zero, add_zero]

theorem finiteReflection_add (r : ι → ℝ) (hr : ∀ j, 0 < r j)
    (c : ι → ℝ) (u v : E → ℝ) :
    finiteReflection r hr c (u+v) = finiteReflection r hr c u + finiteReflection r hr c v := by
  funext x
  simp only [Pi.add_def, finiteReflection, reflectedSample, indicator_add, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]
  ring

theorem finiteReflection_smul (r : ι → ℝ) (hr : ∀ j, 0 < r j)
    (c : ι → ℝ) (a : ℝ) (u : E → ℝ) :
    finiteReflection r hr c (a • u) = a • finiteReflection r hr c u := by
  funext x
  have hi (y : E) : (halfSpace d).indicator (a • u) y = a * (halfSpace d).indicator u y := by
    by_cases hy : y ∈ halfSpace d <;> simp [hy]
  simp only [finiteReflection, reflectedSample, hi, Pi.smul_apply, smul_eq_mul,
    mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem memLp_finiteReflection (r : ι → ℝ) (hr : ∀ j, 0 < r j)
    (c : ι → ℝ) {u : E → ℝ} (hu : MemLp u 2 (volume.restrict (halfSpace d))) :
    MemLp (finiteReflection r hr c u) 2 volume :=
  ((memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hu).add
    (memLp_finsetSum Finset.univ (fun j _ => (memLp_reflectedSample (r j) (hr j) hu).const_mul (c j)))

def finiteReflectionL2Bound (r : ι → ℝ) (c : ι → ℝ) : ℝ≥0∞ :=
  1 + ∑ j, ‖c j‖ₑ * (ENNReal.ofReal (r j)⁻¹) ^ (1/(2:ℝ≥0∞)).toReal

theorem finiteReflectionL2Bound_ne_top (r : ι → ℝ) (c : ι → ℝ) :
    finiteReflectionL2Bound r c ≠ ⊤ := by
  apply ENNReal.add_ne_top.mpr
  refine ⟨by norm_num, ENNReal.sum_ne_top.mpr (fun j _ => ?_)⟩
  exact ENNReal.mul_ne_top (by simp) (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)

theorem eLpNorm_finiteReflection_le (r : ι → ℝ) (hr : ∀ j, 0 < r j)
    (c : ι → ℝ) {u : E → ℝ} (hu : MemLp u 2 (volume.restrict (halfSpace d))) :
    eLpNorm (finiteReflection r hr c u) 2 volume ≤
      finiteReflectionL2Bound r c * eLpNorm u 2 (volume.restrict (halfSpace d)) := by
  let f (j : ι) : E → ℝ := fun x => c j * reflectedSample (r j) (hr j) u x
  have hf (j : ι) := (memLp_reflectedSample (r j) (hr j) hu).const_mul (c j)
  have hs := memLp_finsetSum' Finset.univ (fun j _ => hf j)
  have hi := (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hu
  have heq : finiteReflection r hr c u = (halfSpace d).indicator u + ∑ j, f j := by
    funext x
    simp only [finiteReflection, Pi.add_apply, Finset.sum_apply, f]
  rw [heq]
  calc
    _ ≤ eLpNorm ((halfSpace d).indicator u) 2 volume + ∑ j, eLpNorm (f j) 2 volume :=
      (eLpNorm_add_le hi.1 hs.1 (by norm_num)).trans
        (add_le_add le_rfl (eLpNorm_sum_le (fun j _ => (hf j).1) (by norm_num)))
    _ ≤ eLpNorm u 2 (volume.restrict (halfSpace d)) +
        ∑ j, ‖c j‖ₑ * ((ENNReal.ofReal (r j)⁻¹) ^ (1/(2:ℝ≥0∞)).toReal *
          eLpNorm u 2 (volume.restrict (halfSpace d))) := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict isOpen_halfSpace.measurableSet]
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro j _
      change eLpNorm (c j • reflectedSample (r j) (hr j) u) 2 volume ≤ _
      rw [eLpNorm_const_smul]
      exact mul_le_mul le_rfl (eLpNorm_reflectedSample_le (r j) (hr j) hu) zero_le zero_le
    _ = _ := by simp only [finiteReflectionL2Bound, add_mul, one_mul, Finset.sum_mul, mul_assoc]

theorem integral_finiteReflection (r : ι → ℝ) (hr : ∀ j, 0 < r j)
    (c : ι → ℝ) {u φ : E → ℝ} (hu : MemLp u 2 (volume.restrict (halfSpace d)))
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    (∫ x, finiteReflection r hr c u x * φ x) =
      ∫ x in halfSpace d, u x * (φ x + ∑ j, c j * (r j)⁻¹ * φ ((scaledReflect (r j) (hr j)).symm x)) := by
  have hi := (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hu
  have hI : Integrable (fun x => (halfSpace d).indicator u x * φ x) :=
    hi.locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport hφ hc
  have hJ (j : ι) : Integrable (fun x => c j * (reflectedSample (r j) (hr j) u x * φ x)) :=
    ((memLp_reflectedSample (r j) (hr j) hu).locallyIntegrable (by norm_num)
      |>.integrable_smul_right_of_hasCompactSupport hφ hc).const_mul (c j)
  have hR (j : ι) : Integrable (fun x => c j * (r j)⁻¹ *
      (u x * φ ((scaledReflect (r j) (hr j)).symm x))) (volume.restrict (halfSpace d)) :=
    (hu.locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport
      (hφ.comp (scaledReflect (r j) (hr j)).symm.continuous)
      (hc.comp_homeomorph (scaledReflect (r j) (hr j)).symm.toHomeomorph)).const_mul _
  have hU : Integrable (fun x => u x * φ x) (volume.restrict (halfSpace d)) :=
    hu.locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport hφ hc
  calc
    _ = (∫ x, (halfSpace d).indicator u x * φ x) +
        ∑ j, c j * ∫ x, reflectedSample (r j) (hr j) u x * φ x := by
      simp_rw [finiteReflection, add_mul, Finset.sum_mul, mul_assoc]
      rw [integral_add hI (integrable_finset_sum _ (fun j _ => hJ j)),
        integral_finset_sum _ (fun j _ => hJ j)]
      simp_rw [integral_const_mul]
    _ = (∫ x in halfSpace d, u x * φ x) +
        ∑ j, c j * (r j)⁻¹ * ∫ x in halfSpace d, u x * φ ((scaledReflect (r j) (hr j)).symm x) := by
      simp_rw [integral_reflectedSample, ← mul_assoc]
      congr 1
      rw [← integral_indicator isOpen_halfSpace.measurableSet]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by by_cases hx : x ∈ halfSpace d <;> simp [hx]
    _ = _ := by
      simp_rw [← integral_const_mul]
      rw [← integral_finset_sum _ (fun j _ => hR j),
        ← integral_add hU
          (integrable_finset_sum _ (fun j _ => hR j))]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by simp only [mul_add, Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intro j _; ring

#print axioms finiteReflection_eq_on_halfSpace
#print axioms eLpNorm_finiteReflection_le
#print axioms integral_finiteReflection
end Yamabe3.Analysis.UniformElliptic
