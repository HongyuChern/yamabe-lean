import Yamabe3.Analysis.BoundaryUniformMultiplier
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Explicit weak Sobolev multiplier constant, linear in the actual
coefficient-jet size. In dimension three and order two it is 49 Q.
The weak input need not be smooth. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set MeasureTheory Filter
open scoped ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryLocalization
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem weak_sobolev_multiplier_explicit_bound
    (k : ℕ) {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    {Q : ℝ} (hQ : 0 ≤ Q) :
    ∀ a : E → ℝ, ContDiff ℝ ∞ a →
      (∀ j ≤ k, ∀ x ∈ O, ‖iteratedFDeriv ℝ j a x‖ ≤ Q) →
      ∀ u : E → ℝ, MemWkp k 2 u O →
      iteratedWeakSobolevNorm k 2 (fun x => a x * u x) O ≤
        ((1+2*(d:ℝ≥0∞))^k * ENNReal.ofReal Q) * iteratedWeakSobolevNorm k 2 u O := by
  classical
  induction k with
  | zero =>
    intro a ha hj u hu
    simp only [pow_zero,one_mul,wkpNorm_zero]
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (by simpa using hj 0 le_rfl x hx) (norm_nonneg _)
  | succ k ih =>
    let C : ℝ≥0∞ := (1+2*(d:ℝ≥0∞))^k * ENNReal.ofReal Q
    have hc := ih
    intro a ha hj u hu
    have haK : ∀ j ≤ k, ∀ x ∈ O, ‖iteratedFDeriv ℝ j a x‖ ≤ Q :=
      fun j hjk x hx => hj j (Nat.le_trans hjk (Nat.le_succ k)) x hx
    have hda (i : Fin d) : ContDiff ℝ ∞ (fun x => fderiv ℝ a x (EuclideanSpace.single i 1)) :=
      (ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdj (i : Fin d) : ∀ j ≤ k, ∀ x ∈ O,
        ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ a x (EuclideanSpace.single i 1)) x‖ ≤ Q := by
      intro j hjk x hx
      have hh := norm_iteratedFDeriv_clm_apply_const (n := j) (x := x)
        (c := EuclideanSpace.single i (1 : ℝ))
        (ha.fderiv_right (m := ∞) (by simp)).contDiffAt (by exact_mod_cast le_top)
      rw [EuclideanSpace.norm_single, norm_one, one_mul, norm_iteratedFDeriv_fderiv] at hh
      exact hh.trans (hj (j+1) (by omega) x hx)
    have hp (i : Fin d) := hu.chosenWeakPartial_mem i
    have hau := memWkp_mul_smooth_of_isCompact_closure (k+1) hO hOc hu ha
    have hlow := Poincare.Analysis.Sobolev.Euclidean.wkpNorm_mono_order
      (p := (2 : ℝ≥0∞)) (Nat.le_succ k) u O
    have hbase : eLpNorm (fun x => a x * u x) 2 (volume.restrict O) ≤
        C * iteratedWeakSobolevNorm (k+1) 2 u O := by
      calc
        _ = iteratedWeakSobolevNorm 0 2 (fun x => a x * u x) O := (wkpNorm_zero _ _ _).symm
        _ ≤ iteratedWeakSobolevNorm k 2 (fun x => a x * u x) O :=
          Poincare.Analysis.Sobolev.Euclidean.wkpNorm_mono_order (Nat.zero_le k) _ _
        _ ≤ C * iteratedWeakSobolevNorm k 2 u O := hc a ha haK u hu.le_succ
        _ ≤ _ := by gcongr
    have hpart (i : Fin d) :
        iteratedWeakSobolevNorm k 2 (chosenWeakPartial' 2 i (fun x => a x * u x) O) O ≤
          (C + C) * iteratedWeakSobolevNorm (k+1) 2 u O := by
      rw [wkpNorm_congr_ae (by norm_num) hO (compact_product_chosen_partial_ae hO hOc ha hu.memW1p i)]
      calc
        _ ≤ iteratedWeakSobolevNorm k 2 (fun x => a x * chosenWeakPartial' 2 i u O x) O +
            iteratedWeakSobolevNorm k 2 (fun x => fderiv ℝ a x (EuclideanSpace.single i 1) * u x) O :=
          wkpNorm_add_le (by norm_num) hO
            (memWkp_mul_smooth_of_isCompact_closure k hO hOc (hp i) ha)
            (memWkp_mul_smooth_of_isCompact_closure k hO hOc hu.le_succ (hda i))
        _ ≤ C * iteratedWeakSobolevNorm k 2 (chosenWeakPartial' 2 i u O) O +
            C * iteratedWeakSobolevNorm k 2 u O := add_le_add (hc a ha haK _ (hp i)) (hc _ (hda i) (hdj i) _ hu.le_succ)
        _ ≤ C * iteratedWeakSobolevNorm (k+1) 2 u O +
            C * iteratedWeakSobolevNorm (k+1) 2 u O := by
          apply add_le_add
          · exact mul_le_mul le_rfl (wkpNorm_chosenWeakPartial_le_wkpNorm_succ k 2 u O i) zero_le zero_le
          · exact mul_le_mul le_rfl hlow zero_le zero_le
        _ = _ := (add_mul _ _ _).symm
    rw [wkpNorm_succ_eq]
    calc
      _ ≤ C * iteratedWeakSobolevNorm (k+1) 2 u O +
          ∑ i, (C + C) * iteratedWeakSobolevNorm (k+1) 2 u O :=
        add_le_add hbase (Finset.sum_le_sum fun i _ => hpart i)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,C,pow_succ]
        ring

#print axioms weak_sobolev_multiplier_explicit_bound
end Yamabe3.Analysis.UniformElliptic
