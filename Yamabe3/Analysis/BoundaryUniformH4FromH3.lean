import Yamabe3.Analysis.BoundaryTangentialH4Estimate
import Yamabe3.Analysis.BoundaryFourthDerivativeRecovery

/-! Quantitative H4 from true zero boundary, the original weak equation,
H3 solution and H2 source. Tangential H3 bounds are proved internally. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.BoundaryTangential
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_flat_H4_of_H3_sobolev_estimate
    (B : SmoothEllipticBilinearForm d univ)
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V)) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (u f : E → ℝ),
      MemW01p 2 u (halfSpace d) → MemWkp 3 2 u (halfSpace d) → MemWkp 2 2 f (halfSpace d) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ halfSpace d →
        (∫ x in halfSpace d, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u (halfSpace d) x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in halfSpace d, f x * φ x) →
      MemWkp 4 2 u (V ∩ halfSpace d) ∧
      iteratedWeakSobolevNorm 4 2 u (V ∩ halfSpace d) ≤ K *
        (iteratedWeakSobolevNorm 3 2 u (halfSpace d) + iteratedWeakSobolevNorm 2 2 f (halfSpace d)) := by
  classical
  let H : Set E := halfSpace d
  have hVH : IsOpen (V ∩ H) := hV.inter isOpen_halfSpace
  have hVHc : IsCompact (closure (V ∩ H)) := hVc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  have ht (l : Fin d) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (u f : E → ℝ),
      MemW01p 2 u H → MemWkp 3 2 u H → MemWkp 2 2 f H →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ H →
        (∫ x in H, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u H x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in H, f x * φ x) →
      l ≠ 0 → iteratedWeakSobolevNorm 3 2 (chosenWeakPartial' 2 l u (V ∩ H)) (V ∩ H) ≤
        C * (iteratedWeakSobolevNorm 3 2 u H + iteratedWeakSobolevNorm 2 2 f H) := by
    by_cases hl : l = 0
    · refine ⟨0, by simp, ?_⟩
      intro _ _ _ _ _ _ hn
      exact (hn hl).elim
    · obtain ⟨C, hC, hh⟩ := exists_flat_tangential_H4_estimate B hV hVc l hl
      exact ⟨C, hC, fun u f hu0 hu2 hf heq _ => (hh u f hu0 hu2 hf heq).2⟩
  choose C hC htC using ht
  obtain ⟨Kn, hKn, hn⟩ := exists_normal_H4_recovery_bound B hVH hVHc
  let S : ℝ≥0∞ := ∑ l : Fin d, C l
  have hS : S ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun l _ => hC l)
  refine ⟨Kn * (1+S), by finiteness, ?_⟩
  intro u f hu0 hu2 hf heq
  have hu3 := flat_dirichlet_H4_of_weakEquation B hV hVc hu0 hu2.le_succ hf heq
  have huV := hu2.mono_set (by norm_num : (1 : ℝ≥0∞) ≤ 2) hVH inter_subset_right
  have hfV := hf.mono_set (by norm_num : (1 : ℝ≥0∞) ≤ 2) hVH inter_subset_right
  have heqV := localized_principal_restrict_canonical hVH inter_subset_right hu2.memW1p heq
  let N : ℝ≥0∞ := iteratedWeakSobolevNorm 3 2 u H + iteratedWeakSobolevNorm 2 2 f H
  have hsum : (∑ l ∈ (Finset.univ : Finset (Fin d)).erase 0,
      iteratedWeakSobolevNorm 3 2 (chosenWeakPartial' 2 l u (V ∩ H)) (V ∩ H)) ≤ S*N := by
    calc
      _ ≤ ∑ l ∈ (Finset.univ : Finset (Fin d)).erase 0, C l * N :=
        Finset.sum_le_sum fun l hl => htC l u f hu0 hu2 hf heq (Finset.mem_erase.mp hl).1
      _ ≤ ∑ l : Fin d, C l * N :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => zero_le)
      _ = _ := by simp only [S, Finset.sum_mul]
  refine ⟨hu3, ?_⟩
  calc
    _ ≤ _ := hn u f hu3 hfV heqV
    _ ≤ Kn * (N + S*N) := by
      apply mul_le_mul le_rfl _ zero_le zero_le
      apply add_le_add _ hsum
      exact add_le_add (wkpNorm_mono_set (by norm_num) hVH inter_subset_right hu2)
        (wkpNorm_mono_set (by norm_num) hVH inter_subset_right hf)
    _ = _ := by ring

#print axioms exists_flat_H4_of_H3_sobolev_estimate
end Yamabe3.Analysis.UniformElliptic
