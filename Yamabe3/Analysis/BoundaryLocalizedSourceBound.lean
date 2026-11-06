/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Sobolev/Boundary/Localization/WeakEquation.lean

Adapts the weak cutoff localization and bounds the commutator source in the actual
Sobolev norm.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.BoundaryLocalizedMultiplier
import Yamabe3.Analysis.BoundaryDifferentiatedSourceBound
import PoincareLib.Analysis.Sobolev.Boundary.Localization.WeakEquation

/-! The cutoff commutator source has an actual bounded Sobolev norm.
This uses the original weak equation and the same localized solution. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryLocalization
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem weak_sobolev_norm_sub_le {O : Set E} (hO : IsOpen O) (k : ℕ)
    {u v : E → ℝ} (hu : MemWkp k 2 u O) (hv : MemWkp k 2 v O) :
    iteratedWeakSobolevNorm k 2 (fun x => u x - v x) O ≤
      iteratedWeakSobolevNorm k 2 u O + iteratedWeakSobolevNorm k 2 v O := by
  have hn := wkpNorm_const_smul (by norm_num : (1 : ℝ≥0∞) ≤ 2) hO hv (-1)
  simp only [neg_one_mul, enorm_neg, enorm_one, one_mul] at hn
  simpa only [← sub_eq_add_neg, hn] using wkpNorm_add_le (by norm_num) hO hu
    (MemWkp.neg (by norm_num) hO hv)

theorem exists_localized_source_uniform_bound
    (k : ℕ) {O W : Set E} (hO : IsOpen O) (hW : IsOpen W)
    (a : E → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ W) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (u f : E → ℝ),
      MemWkp (k+1) 2 u (W ∩ O) → MemWkp k 2 f (W ∩ O) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W ∩ O →
        (∫ x in W ∩ O, ∑ i, ∑ j, a x i j * chosenWeakPartial' 2 j u (W ∩ O) x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in W ∩ O, f x * φ x) →
      ∃ F : E → ℝ, MemWkp k 2 F O ∧
        iteratedWeakSobolevNorm k 2 F O ≤ C *
          (iteratedWeakSobolevNorm k 2 f (W ∩ O) + iteratedWeakSobolevNorm (k+1) 2 u (W ∩ O)) ∧
        ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
          (∫ x in O, ∑ i, ∑ j, a x i j *
            chosenWeakPartial' 2 j (fun y => χ y * u y) O x *
            fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, F x * φ x := by
  classical
  let dc (i : Fin d) (x : E) := fderiv ℝ χ x (EuclideanSpace.single i 1)
  let b (i j : Fin d) (x : E) := a x i j * dc j x
  let db (i j : Fin d) (x : E) := fderiv ℝ (b i j) x (EuclideanSpace.single i 1)
  let c (i j : Fin d) (x : E) := a x i j * dc i x
  have hdc (i : Fin d) : ContDiff ℝ ∞ (dc i) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdcs (i : Fin d) : tsupport (dc i) ⊆ W := (tsupport_fderiv_apply_subset ℝ _).trans hs
  have hb (i j : Fin d) : ContDiff ℝ ∞ (b i j) := (ha i j).mul (hdc j)
  have hbs (i j : Fin d) : tsupport (b i j) ⊆ W := tsupport_mul_subset_right.trans (hdcs j)
  have hbc (i j : Fin d) : HasCompactSupport (b i j) := (hc.fderiv_apply ℝ _).mul_left
  have hdb (i j : Fin d) : ContDiff ℝ ∞ (db i j) :=
    ((hb i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdbs (i j : Fin d) : tsupport (db i j) ⊆ W := (tsupport_fderiv_apply_subset ℝ _).trans (hbs i j)
  have hcc (i j : Fin d) : ContDiff ℝ ∞ (c i j) := (ha i j).mul (hdc i)
  have hcs (i j : Fin d) : tsupport (c i j) ⊆ W := tsupport_mul_subset_right.trans (hdcs i)
  obtain ⟨Cf, hCf, hcf⟩ := exists_localized_sobolev_multiplier_bound k hO hW χ hχ hc hs
  choose B hB hbB using fun i j => exists_localized_sobolev_multiplier_bound k hO hW
    (b i j) (hb i j) (hbc i j) (hbs i j)
  choose D hD hbD using fun i j => exists_localized_sobolev_multiplier_bound k hO hW
    (db i j) (hdb i j) ((hbc i j).fderiv_apply ℝ _) (hdbs i j)
  choose A hA hbA using fun i j => exists_localized_sobolev_multiplier_bound k hO hW
    (c i j) (hcc i j) ((hc.fderiv_apply ℝ _).mul_left) (hcs i j)
  let Cu : ℝ≥0∞ := ∑ i, ∑ j, (D i j + B i j + A i j)
  have hCu : Cu ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => ENNReal.sum_ne_top.mpr fun j _ =>
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hD i j, hB i j⟩, hA i j⟩
  refine ⟨Cf + Cu, ENNReal.add_ne_top.mpr ⟨hCf, hCu⟩, ?_⟩
  intro u f hu hf heq
  let p (i : Fin d) := chosenWeakPartial' 2 i u (W ∩ O)
  let G (i j : Fin d) (x : E) := db i j x * u x + b i j x * p i x + c i j x * p j x
  let F : E → ℝ := fun x => χ x * f x - ∑ i, ∑ j, G i j x
  have hp (i : Fin d) := hu.chosenWeakPartial_mem i
  have h1 (i j : Fin d) := memWkp_mul_smooth_of_tsupport_subset k hO hW hu.le_succ
    (hdb i j) ((hbc i j).fderiv_apply ℝ _) (hdbs i j)
  have h2 (i j : Fin d) := memWkp_mul_smooth_of_tsupport_subset k hO hW (hp i) (hb i j) (hbc i j) (hbs i j)
  have h3 (i j : Fin d) := memWkp_mul_smooth_of_tsupport_subset k hO hW (hp j) (hcc i j)
    ((hc.fderiv_apply ℝ _).mul_left) (hcs i j)
  have hG (i j : Fin d) : MemWkp k 2 (G i j) O :=
    MemWkp.add (by norm_num) hO (MemWkp.add (by norm_num) hO (h1 i j) (h2 i j)) (h3 i j)
  have hsum := finite_sobolev_sum_with_bound hO k Finset.univ (fun i x => ∑ j, G i j x)
    (fun i _ => (finite_sobolev_sum_with_bound hO k Finset.univ (G i) (fun j _ => hG i j)).1)
  have hχf := memWkp_mul_smooth_of_tsupport_subset k hO hW hf hχ hc hs
  have hGn (i j : Fin d) : iteratedWeakSobolevNorm k 2 (G i j) O ≤
      (D i j + B i j + A i j) * iteratedWeakSobolevNorm (k+1) 2 u (W ∩ O) := by
    have hlow := Poincare.Analysis.Sobolev.Euclidean.wkpNorm_mono_order (p := (2 : ℝ≥0∞))
      (Nat.le_succ k) u (W ∩ O)
    calc
      _ ≤ (iteratedWeakSobolevNorm k 2 (fun x => db i j x * u x) O +
          iteratedWeakSobolevNorm k 2 (fun x => b i j x * p i x) O) +
          iteratedWeakSobolevNorm k 2 (fun x => c i j x * p j x) O :=
        (wkpNorm_add_le (by norm_num) hO (MemWkp.add (by norm_num) hO (h1 i j) (h2 i j)) (h3 i j)).trans
          (add_le_add (wkpNorm_add_le (by norm_num) hO (h1 i j) (h2 i j)) le_rfl)
      _ ≤ (D i j * iteratedWeakSobolevNorm k 2 u (W ∩ O) +
          B i j * iteratedWeakSobolevNorm k 2 (p i) (W ∩ O)) +
          A i j * iteratedWeakSobolevNorm k 2 (p j) (W ∩ O) :=
        add_le_add (add_le_add (hbD i j _ hu.le_succ) (hbB i j _ (hp i))) (hbA i j _ (hp j))
      _ ≤ (D i j * iteratedWeakSobolevNorm (k+1) 2 u (W ∩ O) +
          B i j * iteratedWeakSobolevNorm (k+1) 2 u (W ∩ O)) +
          A i j * iteratedWeakSobolevNorm (k+1) 2 u (W ∩ O) := by
        apply add_le_add
        · exact add_le_add (mul_le_mul le_rfl hlow zero_le zero_le)
            (mul_le_mul le_rfl (wkpNorm_chosenWeakPartial_le_wkpNorm_succ k 2 u (W ∩ O) i) zero_le zero_le)
        · exact mul_le_mul le_rfl (wkpNorm_chosenWeakPartial_le_wkpNorm_succ k 2 u (W ∩ O) j) zero_le zero_le
      _ = _ := by ring
  refine ⟨F, MemWkp.sub (by norm_num) hO hχf hsum.1, ?_, ?_⟩
  · calc
      _ ≤ iteratedWeakSobolevNorm k 2 (fun x => χ x * f x) O +
          iteratedWeakSobolevNorm k 2 (fun x => ∑ i, ∑ j, G i j x) O := weak_sobolev_norm_sub_le hO k hχf hsum.1
      _ ≤ Cf * iteratedWeakSobolevNorm k 2 f (W ∩ O) + ∑ i, ∑ j, iteratedWeakSobolevNorm k 2 (G i j) O :=
        add_le_add (hcf f hf) (hsum.2.trans (Finset.sum_le_sum fun i _ =>
          (finite_sobolev_sum_with_bound hO k Finset.univ (G i) (fun j _ => hG i j)).2))
      _ ≤ Cf * iteratedWeakSobolevNorm k 2 f (W ∩ O) + ∑ i, ∑ j,
          (D i j + B i j + A i j) * iteratedWeakSobolevNorm (k+1) 2 u (W ∩ O) := by
        gcongr with i _ j _; exact hGn i j
      _ = Cf * iteratedWeakSobolevNorm k 2 f (W ∩ O) + Cu * iteratedWeakSobolevNorm (k+1) 2 u (W ∩ O) := by
        simp only [Cu, Finset.sum_mul]
      _ ≤ _ := by
        calc
          _ ≤ (Cf + Cu) * iteratedWeakSobolevNorm k 2 f (W ∩ O) +
              (Cf + Cu) * iteratedWeakSobolevNorm (k+1) 2 u (W ∩ O) := by gcongr <;> simp
          _ = _ := (mul_add _ _ _).symm
  · have hh := (localize_weak_divergence k hO hW a ha hu hf hχ hc hs heq).2
    intro φ hφ hcφ hsφ
    rw [hh φ hφ hcφ hsφ]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      apply congrArg (fun z : ℝ => z * φ x)
      dsimp only [F, G, db, b, c, dc, p]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

#print axioms weak_sobolev_norm_sub_le
#print axioms exists_localized_source_uniform_bound
end Yamabe3.Analysis.UniformElliptic
