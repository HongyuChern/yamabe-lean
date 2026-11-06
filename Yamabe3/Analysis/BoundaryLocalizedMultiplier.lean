import Yamabe3.Analysis.BoundarySobolevMultiplier

/-! Quantitative cutoff localization across the smaller chart boundary.
The cutoff may be nonzero on the genuine boundary of the larger domain. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set MeasureTheory Filter
open scoped ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryLocalization
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem localized_product_chosen_partial_ae {O W : Set E}
    (hO : IsOpen O) (hW : IsOpen W) {χ u : E → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ W)
    (hu : MemW1p 2 u (W ∩ O)) (i : Fin d) :
    chosenWeakPartial' 2 i (fun x => χ x * u x) O =ᵐ[volume.restrict O]
      (fun x => χ x * chosenWeakPartial' 2 i u (W ∩ O) x +
        fderiv ℝ χ x (EuclideanSpace.single i 1) * u x) := by
  have hau := (memWkp_mul_smooth_of_tsupport_subset 1 hO hW
    ((MemWkp.one_iff_memW1p).mpr hu) hχ hc hs).memW1p
  have hp := chosenWeakPartial'_memLp_of_mem hu i
  have hdχ : ContDiff ℝ ∞ (fun x => fderiv ℝ χ x (EuclideanSpace.single i 1)) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hr : MemLp (fun x => χ x * chosenWeakPartial' 2 i u (W ∩ O) x +
      fderiv ℝ χ x (EuclideanSpace.single i 1) * u x) 2 (volume.restrict O) :=
    (memWkp_mul_smooth_of_tsupport_subset 0 hO hW hp hχ hc hs).memLp.add
      (memWkp_mul_smooth_of_tsupport_subset 0 hO hW hu.1 hdχ (hc.fderiv_apply ℝ _)
        ((tsupport_fderiv_apply_subset ℝ _).trans hs)).memLp
  exact HasWeakPartialDeriv.ae_eq hO
    (chosenWeakPartial'_isWeakPartial_of_mem hau i)
    (hasWeakPartialDeriv_mul_smooth_of_tsupport_subset hW i hu.1 hp
      (chosenWeakPartial'_isWeakPartial_of_mem hu i) hχ hc hs)
    ((chosenWeakPartial'_memLp_of_mem hau i).locallyIntegrable (by norm_num))
    (hr.locallyIntegrable (by norm_num))

theorem exists_localized_sobolev_multiplier_bound
    (k : ℕ) {O W : Set E} (hO : IsOpen O) (hW : IsOpen W)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ W) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : E → ℝ, MemWkp k 2 u (W ∩ O) →
      iteratedWeakSobolevNorm k 2 (fun x => χ x * u x) O ≤
        C * iteratedWeakSobolevNorm k 2 u (W ∩ O) := by
  classical
  induction k generalizing χ with
  | zero =>
    obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hχ.continuous
    refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, ?_⟩
    intro u hu
    simp only [wkpNorm_zero]
    have he : W.indicator (fun x => χ x * u x) = (fun x => χ x * u x) := by
      funext x
      by_cases hx : x ∈ W
      · simp only [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), zero_mul]
    calc
      _ = eLpNorm (W.indicator (fun x => χ x * u x)) 2 (volume.restrict O) := by rw [he]
      _ = eLpNorm (fun x => χ x * u x) 2 (volume.restrict (W ∩ O)) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hW.measurableSet, Measure.restrict_restrict hW.measurableSet]
      _ ≤ _ := by
        apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        exact Eventually.of_forall fun x => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  | succ k ih =>
    obtain ⟨C, hC, hcB⟩ := ih χ hχ hc hs
    have hdχ (i : Fin d) : ContDiff ℝ ∞ (fun x => fderiv ℝ χ x (EuclideanSpace.single i 1)) :=
      (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    choose D hD hd using fun i => ih _ (hdχ i) (hc.fderiv_apply ℝ _)
      ((tsupport_fderiv_apply_subset ℝ _).trans hs)
    refine ⟨C + ∑ i, (C + D i), ENNReal.add_ne_top.mpr
      ⟨hC, ENNReal.sum_ne_top.mpr (fun i _ => ENNReal.add_ne_top.mpr ⟨hC, hD i⟩)⟩, ?_⟩
    intro u hu
    have hp (i : Fin d) := hu.chosenWeakPartial_mem i
    have hlow := Poincare.Analysis.Sobolev.Euclidean.wkpNorm_mono_order
      (p := (2 : ℝ≥0∞)) (Nat.le_succ k) u (W ∩ O)
    have hbase : eLpNorm (fun x => χ x * u x) 2 (volume.restrict O) ≤
        C * iteratedWeakSobolevNorm (k+1) 2 u (W ∩ O) := by
      calc
        _ = iteratedWeakSobolevNorm 0 2 (fun x => χ x * u x) O := (wkpNorm_zero _ _ _).symm
        _ ≤ iteratedWeakSobolevNorm k 2 (fun x => χ x * u x) O :=
          Poincare.Analysis.Sobolev.Euclidean.wkpNorm_mono_order (Nat.zero_le k) _ _
        _ ≤ C * iteratedWeakSobolevNorm k 2 u (W ∩ O) := hcB u hu.le_succ
        _ ≤ _ := by gcongr
    have hpart (i : Fin d) :
        iteratedWeakSobolevNorm k 2 (chosenWeakPartial' 2 i (fun x => χ x * u x) O) O ≤
          (C + D i) * iteratedWeakSobolevNorm (k+1) 2 u (W ∩ O) := by
      rw [wkpNorm_congr_ae (by norm_num) hO
        (localized_product_chosen_partial_ae hO hW hχ hc hs hu.memW1p i)]
      calc
        _ ≤ iteratedWeakSobolevNorm k 2 (fun x => χ x * chosenWeakPartial' 2 i u (W ∩ O) x) O +
            iteratedWeakSobolevNorm k 2 (fun x => fderiv ℝ χ x (EuclideanSpace.single i 1) * u x) O :=
          wkpNorm_add_le (by norm_num) hO
            (memWkp_mul_smooth_of_tsupport_subset k hO hW (hp i) hχ hc hs)
            (memWkp_mul_smooth_of_tsupport_subset k hO hW hu.le_succ (hdχ i) (hc.fderiv_apply ℝ _)
              ((tsupport_fderiv_apply_subset ℝ _).trans hs))
        _ ≤ C * iteratedWeakSobolevNorm k 2 (chosenWeakPartial' 2 i u (W ∩ O)) (W ∩ O) +
            D i * iteratedWeakSobolevNorm k 2 u (W ∩ O) := add_le_add (hcB _ (hp i)) (hd i _ hu.le_succ)
        _ ≤ C * iteratedWeakSobolevNorm (k+1) 2 u (W ∩ O) +
            D i * iteratedWeakSobolevNorm (k+1) 2 u (W ∩ O) :=
          add_le_add (mul_le_mul le_rfl (wkpNorm_chosenWeakPartial_le_wkpNorm_succ k 2 u (W ∩ O) i) zero_le zero_le)
            (mul_le_mul le_rfl hlow zero_le zero_le)
        _ = _ := (add_mul _ _ _).symm
    rw [wkpNorm_succ_eq]
    calc
      _ ≤ C * iteratedWeakSobolevNorm (k+1) 2 u (W ∩ O) +
          ∑ i, (C + D i) * iteratedWeakSobolevNorm (k+1) 2 u (W ∩ O) :=
        add_le_add hbase (Finset.sum_le_sum fun i _ => hpart i)
      _ = _ := by rw [add_mul, Finset.sum_mul]

#print axioms localized_product_chosen_partial_ae
#print axioms exists_localized_sobolev_multiplier_bound
end Yamabe3.Analysis.UniformElliptic
