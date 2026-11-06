import Yamabe3.Analysis.BoundaryThirdDerivativeRecovery

/-! Quantitative fourth-order normal recovery. Mixed derivatives retain
same-function identities; the differentiated source is constructed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set MeasureTheory Filter
open scoped ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_normal_H4_recovery_bound
    (B : SmoothEllipticBilinearForm d univ)
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O)) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (u f : E → ℝ),
      MemWkp 4 2 u O → MemWkp 2 2 f O →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
        (∫ x in O, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u O x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x) →
      iteratedWeakSobolevNorm 4 2 u O ≤ K *
        (iteratedWeakSobolevNorm 3 2 u O + iteratedWeakSobolevNorm 2 2 f O +
          ∑ k ∈ (Finset.univ : Finset (Fin d)).erase 0,
            iteratedWeakSobolevNorm 3 2 (chosenWeakPartial' 2 k u O) O) := by
  classical
  obtain ⟨Cd, hCd, hdiff⟩ := exists_differentiated_source_uniform_bound 1 hO hOc B.a B.smooth_a 0
  obtain ⟨Kn, hKn, hn⟩ := exists_normal_H3_recovery_bound B hO hOc
  refine ⟨2 + Kn*(3+Cd), by finiteness, ?_⟩
  intro u f hu hf heq
  let p (i : Fin d) := chosenWeakPartial' 2 i u O
  let T : ℝ≥0∞ := ∑ k ∈ (Finset.univ : Finset (Fin d)).erase 0, iteratedWeakSobolevNorm 3 2 (p k) O
  let N : ℝ≥0∞ := iteratedWeakSobolevNorm 3 2 u O + iteratedWeakSobolevNorm 2 2 f O + T
  have hU : iteratedWeakSobolevNorm 3 2 u O ≤ N := (le_add_right le_rfl).trans (le_add_right le_rfl)
  have hF : iteratedWeakSobolevNorm 2 2 f O ≤ N := (le_add_left le_rfl).trans (le_add_right le_rfl)
  have hT : T ≤ N := le_add_left le_rfl
  obtain ⟨F, hFm, hFn, hFeq⟩ := hdiff u f hu.le_succ hf heq
  have hFN : iteratedWeakSobolevNorm 1 2 F O ≤ (1+Cd)*N := by
    calc
      _ ≤ _ := hFn
      _ ≤ N + Cd*N := add_le_add hF (mul_le_mul le_rfl hU zero_le zero_le)
      _ = _ := by ring
  have hPN : iteratedWeakSobolevNorm 2 2 (p 0) O ≤ N :=
    (wkpNorm_chosenWeakPartial_le_wkpNorm_succ 2 2 u O 0).trans hU
  have htan : (∑ k ∈ (Finset.univ : Finset (Fin d)).erase 0,
      iteratedWeakSobolevNorm 2 2 (chosenWeakPartial' 2 k (p 0) O) O) ≤ N := by
    apply LE.le.trans _ hT
    apply Finset.sum_le_sum
    intro k hk
    rw [wkpNorm_congr_ae (by norm_num) hO (chosen_weak_hessian_commute_ae hO hu.le_succ.le_succ k 0)]
    exact wkpNorm_chosenWeakPartial_le_wkpNorm_succ 2 2 (p k) O 0
  have hp0 : iteratedWeakSobolevNorm 3 2 (p 0) O ≤ Kn*(3+Cd)*N := by
    calc
      _ ≤ _ := hn (p 0) F (hu.chosenWeakPartial_mem 0) hFm hFeq
      _ ≤ Kn*(N+(1+Cd)*N+N) := by gcongr
      _ = _ := by ring
  have h0 : eLpNorm u 2 (volume.restrict O) ≤ N := by
    rw [← wkpNorm_zero]
    exact (Poincare.Analysis.Sobolev.Euclidean.wkpNorm_mono_order (Nat.zero_le 3) u O).trans hU
  rw [wkpNorm_succ_eq 3, ← Finset.sum_erase_add Finset.univ
    (fun k => iteratedWeakSobolevNorm 3 2 (p k) O) (Finset.mem_univ 0)]
  change _ ≤ (2 + Kn*(3+Cd))*N
  calc
    _ ≤ N + (N + Kn*(3+Cd)*N) := add_le_add h0 (add_le_add hT hp0)
    _ = _ := by ring

#print axioms exists_normal_H4_recovery_bound
end Yamabe3.Analysis.UniformElliptic
