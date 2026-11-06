import Yamabe3.Analysis.BoundaryH2SobolevEstimate
import Yamabe3.Analysis.BoundaryDifferentiatedSourceBound

/-! Quantitative third-order normal recovery from the differentiated
original equation. Tangential norms are explicitly retained for subsequent
boundary estimates, not asserted to be produced by this auxiliary result. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set MeasureTheory Filter
open scoped ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem chosen_third_partial_reorder {O : Set E} (hO : IsOpen O)
    {u : E → ℝ} (hu : MemWkp 3 2 u O) (i j k : Fin d) :
    chosenWeakPartial' 2 i (chosenWeakPartial' 2 j (chosenWeakPartial' 2 k u O) O) O =ᵐ[volume.restrict O]
      chosenWeakPartial' 2 j (chosenWeakPartial' 2 k (chosenWeakPartial' 2 i u O) O) O :=
  (chosen_weak_hessian_commute_ae hO (hu.chosenWeakPartial_mem k) i j).trans
    (chosenWeakPartial'_ae_congr (by norm_num) hO
      (chosen_weak_hessian_commute_ae hO hu.le_succ i k) j)

theorem exists_normal_H3_recovery_bound
    (B : SmoothEllipticBilinearForm d univ)
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O)) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (u f : E → ℝ),
      MemWkp 3 2 u O → MemWkp 1 2 f O →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
        (∫ x in O, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u O x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x) →
      iteratedWeakSobolevNorm 3 2 u O ≤ K *
        (iteratedWeakSobolevNorm 2 2 u O + iteratedWeakSobolevNorm 1 2 f O +
          ∑ k ∈ (Finset.univ : Finset (Fin d)).erase 0,
            iteratedWeakSobolevNorm 2 2 (chosenWeakPartial' 2 k u O) O) := by
  classical
  obtain ⟨Cf, hCf, hdiff⟩ := exists_differentiated_source_uniform_bound 0 hO hOc B.a B.smooth_a 0
  obtain ⟨A, D, hA, hD, hhess⟩ := exists_uniform_hessian_bound_from_tangential B hO hOc
  let L : ℝ≥0∞ := 1 + ENNReal.ofReal B.lam⁻¹ *
    ((1 + Cf) + ENNReal.ofReal A * ((d : ℝ≥0∞) * d) + ENNReal.ofReal D * ((d : ℝ≥0∞) * d))
  let K0 : ℝ≥0∞ := 1 + (d : ℝ≥0∞) * d * L
  refine ⟨2 + K0, by dsimp [K0, L]; finiteness, ?_⟩
  intro u f hu hf heq
  let p (i : Fin d) := chosenWeakPartial' 2 i u O
  let T : ℝ≥0∞ := ∑ k ∈ (Finset.univ : Finset (Fin d)).erase 0, iteratedWeakSobolevNorm 2 2 (p k) O
  let N : ℝ≥0∞ := iteratedWeakSobolevNorm 2 2 u O + iteratedWeakSobolevNorm 1 2 f O + T
  have hU : iteratedWeakSobolevNorm 2 2 u O ≤ N := (le_add_right le_rfl).trans (le_add_right le_rfl)
  have hF : iteratedWeakSobolevNorm 1 2 f O ≤ N := (le_add_left le_rfl).trans (le_add_right le_rfl)
  have hT : T ≤ N := le_add_left le_rfl
  obtain ⟨F, hFmem, hFn, hFeq⟩ := hdiff u f hu.le_succ hf heq
  have hFbound : eLpNorm F 2 (volume.restrict O) ≤ (1+Cf) * N := by
    rw [← wkpNorm_zero 2 F O]
    calc
      _ ≤ _ := hFn
      _ ≤ N + Cf * N := add_le_add hF (mul_le_mul le_rfl hU zero_le zero_le)
      _ = _ := by ring
  have htan (k : Fin d) (hk : k ≠ 0) (i : Fin d) :
      eLpNorm (chosenWeakPartial' 2 k (chosenWeakPartial' 2 i (p 0) O) O) 2 (volume.restrict O) ≤ T := by
    rw [eLpNorm_congr_ae (chosen_third_partial_reorder hO hu k i 0)]
    have hnorm : eLpNorm (chosenWeakPartial' 2 i (chosenWeakPartial' 2 0 (p k) O) O) 2 (volume.restrict O) ≤
        iteratedWeakSobolevNorm 2 2 (p k) O := by
      rw [← wkpNorm_zero]
      exact (wkpNorm_chosenWeakPartial_le_wkpNorm_succ 0 2 (chosenWeakPartial' 2 0 (p k) O) O i).trans
        (wkpNorm_chosenWeakPartial_le_wkpNorm_succ 1 2 (p k) O 0)
    apply hnorm.trans
    exact Finset.single_le_sum
      (f := fun k : Fin d => iteratedWeakSobolevNorm 2 2 (p k) O) (fun _ _ => zero_le)
      (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
  have hpn (j : Fin d) : eLpNorm (chosenWeakPartial' 2 j (p 0) O) 2 (volume.restrict O) ≤ N := by
    rw [← wkpNorm_zero]
    exact ((wkpNorm_chosenWeakPartial_le_wkpNorm_succ 0 2 (p 0) O j).trans
      (wkpNorm_chosenWeakPartial_le_wkpNorm_succ 1 2 u O 0)).trans hU
  have hpSum : (∑ ij : Fin d × Fin d, eLpNorm (chosenWeakPartial' 2 ij.2 (p 0) O) 2 (volume.restrict O)) ≤
      (d : ℝ≥0∞) * d * N := by
    calc
      _ ≤ ∑ _ij : Fin d × Fin d, N := Finset.sum_le_sum fun ij _ => hpn ij.2
      _ = _ := by simp [Nat.cast_mul, mul_assoc]
  have hess (i j : Fin d) : eLpNorm (chosenWeakPartial' 2 i (chosenWeakPartial' 2 j (p 0) O) O) 2 (volume.restrict O) ≤ L * N := by
    have h := hhess (p 0) F (hu.chosenWeakPartial_mem 0) hFmem hFeq T htan i j
    calc
      _ ≤ _ := h
      _ ≤ N + ENNReal.ofReal B.lam⁻¹ *
          ((1+Cf)*N + ENNReal.ofReal A*((d : ℝ≥0∞)*d*N) + ENNReal.ofReal D*((d : ℝ≥0∞)*d*N)) := by gcongr
      _ = L * N := by dsimp only [L]; ring
  have hp0 : iteratedWeakSobolevNorm 2 2 (p 0) O ≤ K0 * N := by
    rw [wkpNorm_two_eq_one_add_hessian]
    calc
      _ ≤ N + ∑ _j : Fin d, ∑ _i : Fin d, L * N :=
        add_le_add ((wkpNorm_chosenWeakPartial_le_wkpNorm_succ 1 2 u O 0).trans hU)
          (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hess i j)
      _ = _ := by dsimp only [K0]; simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have h0 : eLpNorm u 2 (volume.restrict O) ≤ N := by
    rw [← wkpNorm_zero]
    exact (Poincare.Analysis.Sobolev.Euclidean.wkpNorm_mono_order (Nat.zero_le 2) u O).trans hU
  rw [wkpNorm_succ_eq 2, ← Finset.sum_erase_add Finset.univ
    (fun k => iteratedWeakSobolevNorm 2 2 (p k) O) (Finset.mem_univ 0)]
  change _ ≤ (2 + K0) * N
  calc
    _ ≤ N + (N + K0 * N) := add_le_add h0 (add_le_add hT hp0)
    _ = _ := by ring

#print axioms chosen_third_partial_reorder
#print axioms exists_normal_H3_recovery_bound
end Yamabe3.Analysis.UniformElliptic
