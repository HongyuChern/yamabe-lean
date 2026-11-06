/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Sobolev/Boundary/DifferentiatedEquation.lean

Extracts the compact-coefficient L2 multiplication argument into a private helper for
Sobolev multiplication.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.BoundaryHessianEquation
import PoincareLib.Analysis.Sobolev.Boundary.Localization.Sobolev
import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Embedding.ExponentIteration

/-! A fixed smooth multiplier on a fixed precompact domain is bounded in
the actual weak Sobolev norm. The constant precedes the multiplied input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryLocalization
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem compact_mul_memLp {O : Set E} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) {a v : E → ℝ} (ha : Continuous a)
    (hv : MemLp v 2 (volume.restrict O)) : MemLp (fun x => a x * v x) 2 (volume.restrict O) := by
  obtain ⟨C, hC⟩ := hOc.exists_bound_of_continuousOn ha.continuousOn
  apply hv.of_le_mul (c := C) (ha.aestronglyMeasurable.mul hv.1)
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x (subset_closure hx)) (norm_nonneg _)

/-- The actual product derivative, with all terms justified in L2. -/
theorem compact_product_chosen_partial_ae {O : Set E} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) {a u : E → ℝ} (ha : ContDiff ℝ ∞ a)
    (hu : MemW1p 2 u O) (i : Fin d) :
    chosenWeakPartial' 2 i (fun x => a x * u x) O =ᵐ[volume.restrict O]
      (fun x => a x * chosenWeakPartial' 2 i u O x +
        fderiv ℝ a x (EuclideanSpace.single i 1) * u x) := by
  have hu1 : MemWkp 1 2 u O := (MemWkp.one_iff_memW1p).mpr hu
  have hau := (memWkp_mul_smooth_of_isCompact_closure 1 hO hOc hu1 ha).memW1p
  have hp := chosenWeakPartial'_memLp_of_mem hu i
  have hda : Continuous (fun x => fderiv ℝ a x (EuclideanSpace.single i 1)) :=
    ((ha.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hr := (compact_mul_memLp hO hOc ha.continuous hp).add (compact_mul_memLp hO hOc hda hu.1)
  exact HasWeakPartialDeriv.ae_eq hO
    (chosenWeakPartial'_isWeakPartial_of_mem hau i)
    ((chosenWeakPartial'_isWeakPartial_of_mem hu i).mul_smooth hO ha
      (hu.1.locallyIntegrable (by norm_num)) (hp.locallyIntegrable (by norm_num)))
    ((chosenWeakPartial'_memLp_of_mem hau i).locallyIntegrable (by norm_num))
    (hr.locallyIntegrable (by norm_num))

/-- Every constant is chosen before the weak Sobolev input. This bound is
for a fixed coefficient and domain; no parameter-family uniformity is implied. -/
theorem exists_compact_sobolev_multiplier_bound
    (k : ℕ) {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (a : E → ℝ) (ha : ContDiff ℝ ∞ a) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : E → ℝ, MemWkp k 2 u O →
      iteratedWeakSobolevNorm k 2 (fun x => a x * u x) O ≤ C * iteratedWeakSobolevNorm k 2 u O := by
  classical
  induction k generalizing a with
  | zero =>
    obtain ⟨C, hC⟩ := hOc.exists_bound_of_continuousOn ha.continuous.continuousOn
    refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, ?_⟩
    intro u hu
    simp only [wkpNorm_zero]
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC x (subset_closure hx)) (norm_nonneg _)
  | succ k ih =>
    obtain ⟨C, hC, hc⟩ := ih a ha
    have hda (i : Fin d) : ContDiff ℝ ∞ (fun x => fderiv ℝ a x (EuclideanSpace.single i 1)) :=
      (ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    choose D hD hd using fun i => ih _ (hda i)
    refine ⟨C + ∑ i, (C + D i), ENNReal.add_ne_top.mpr
      ⟨hC, ENNReal.sum_ne_top.mpr (fun i _ => ENNReal.add_ne_top.mpr ⟨hC, hD i⟩)⟩, ?_⟩
    intro u hu
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
        _ ≤ C * iteratedWeakSobolevNorm k 2 u O := hc u hu.le_succ
        _ ≤ _ := by gcongr
    have hpart (i : Fin d) :
        iteratedWeakSobolevNorm k 2 (chosenWeakPartial' 2 i (fun x => a x * u x) O) O ≤
          (C + D i) * iteratedWeakSobolevNorm (k+1) 2 u O := by
      rw [wkpNorm_congr_ae (by norm_num) hO (compact_product_chosen_partial_ae hO hOc ha hu.memW1p i)]
      calc
        _ ≤ iteratedWeakSobolevNorm k 2 (fun x => a x * chosenWeakPartial' 2 i u O x) O +
            iteratedWeakSobolevNorm k 2 (fun x => fderiv ℝ a x (EuclideanSpace.single i 1) * u x) O :=
          wkpNorm_add_le (by norm_num) hO
            (memWkp_mul_smooth_of_isCompact_closure k hO hOc (hp i) ha)
            (memWkp_mul_smooth_of_isCompact_closure k hO hOc hu.le_succ (hda i))
        _ ≤ C * iteratedWeakSobolevNorm k 2 (chosenWeakPartial' 2 i u O) O +
            D i * iteratedWeakSobolevNorm k 2 u O := add_le_add (hc _ (hp i)) (hd i _ hu.le_succ)
        _ ≤ C * iteratedWeakSobolevNorm (k+1) 2 u O +
            D i * iteratedWeakSobolevNorm (k+1) 2 u O := by
          apply add_le_add
          · exact mul_le_mul le_rfl (wkpNorm_chosenWeakPartial_le_wkpNorm_succ k 2 u O i) zero_le zero_le
          · exact mul_le_mul le_rfl hlow zero_le zero_le
        _ = _ := (add_mul _ _ _).symm
    rw [wkpNorm_succ_eq]
    calc
      _ ≤ C * iteratedWeakSobolevNorm (k+1) 2 u O +
          ∑ i, (C + D i) * iteratedWeakSobolevNorm (k+1) 2 u O :=
        add_le_add hbase (Finset.sum_le_sum fun i _ => hpart i)
      _ = _ := by rw [add_mul, Finset.sum_mul]

#print axioms compact_product_chosen_partial_ae
#print axioms exists_compact_sobolev_multiplier_bound
end Yamabe3.Analysis.UniformElliptic
