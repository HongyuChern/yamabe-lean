import Yamabe3.Analysis.UniformElliptic.LocalStrongWeakCompletion
import Yamabe3.Analysis.UniformElliptic.ClassicalCoordinateLpBound

/-!
# Actual local comparison of classical profiles and weak Sobolev norms

No zero boundary values are assumed. A genuine compact smooth extension
near the retained closure permits identification of the classical jets
with the actual weak jets by restriction. The classical profile is bounded
by the weak-coordinate sum with constant one; the reverse bound records
the exact number of coordinate tuples. These are proved comparisons, not
a silently assumed equality of norms.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic.InteriorEstimates
open Poincare.Analysis.Sobolev.Euclidean
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem local_profile_le_actual_weak_norm
    {V O : Set E3} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hO : IsOpen O) (hVO : closure V ⊆ O)
    {u : E3 → ℝ} (hu : ContDiffOn ℝ ∞ u O) (k : ℕ) :
    derivativeProfile 2 V k u ≤ iteratedWeakSobolevNorm k 2 u V := by
  classical
  obtain ⟨v, hv, hvc, hve⟩ := exists_smooth_compact_extension_near_compact hO hVc hVO hu
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hae : v =ᵐ[volume.restrict V] u := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    exact (hve x (subset_closure hx)).self_of_nhds
  have hweak (j : ℕ) (β : Fin j → Fin 3) :
      iterWeakPartial 2 j β u V =ᵐ[volume.restrict V] iterClassicalPartial j β v := by
    have hvW : MemWkp j 2 v univ := MemWkp_of_smooth_compactSupport
      isOpen_univ hv hvc (subset_univ _) hp j
    have hg : iterWeakPartial 2 j β v univ =ᵐ[volume] iterClassicalPartial j β v := by
      simpa only [Measure.restrict_univ] using
        iterWeakPartial_smooth_ae_eq_iterClassicalPartial hp isOpen_univ j β
          hv hvc (subset_univ _)
    have hl : iterWeakPartial 2 j β v univ =ᵐ[volume.restrict V]
        iterWeakPartial 2 j β v V :=
      iterWeakPartial_mono_set_ae hp hV (subset_univ _) β hvW
    have hc : iterWeakPartial 2 j β v V =ᵐ[volume.restrict V]
        iterWeakPartial 2 j β u V := iterWeakPartial_ae_congr hp hV j β hae
    exact hc.symm.trans (hl.symm.trans (ae_restrict_of_ae hg))
  have hprofile := derivativeProfile_eq_of_local_germs hV.measurableSet
    (fun x hx => hve x (subset_closure hx)) 2 k
  rw [← hprofile, derivativeProfile, wkpNorm_eq_sum]
  apply Finset.sum_le_sum
  intro j hj
  apply (ClassicalCoordinateBounds.eLpNorm_iteratedFDeriv_le_sum_iterClassicalPartial j hp hv V).trans
  apply Finset.sum_le_sum
  intro β _
  exact le_of_eq (eLpNorm_congr_ae (hweak j β).symm)

theorem actual_weak_norm_le_local_profile
    {V O : Set E3} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hO : IsOpen O) (hVO : closure V ⊆ O)
    {u : E3 → ℝ} (hu : ContDiffOn ℝ ∞ u O) (k : ℕ) :
    iteratedWeakSobolevNorm k 2 u V ≤
      (∑ j ∈ Finset.range (k + 1), (Fintype.card (Fin j → Fin 3) : ℝ≥0∞)) *
        derivativeProfile 2 V k u := by
  classical
  rw [wkpNorm_eq_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  calc
    _ ≤ ∑ _β : Fin j → Fin 3, derivativeProfile 2 V k u :=
      Finset.sum_le_sum (fun β _ => eLpNorm_weak_jet_le_local_profile hV hVc hO hVO hu
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) β)
    _ = (Fintype.card (Fin j → Fin 3) : ℝ≥0∞) * derivativeProfile 2 V k u := by
      simp [nsmul_eq_mul]

#print axioms local_profile_le_actual_weak_norm
#print axioms actual_weak_norm_le_local_profile

end Yamabe3.Analysis.UniformElliptic
