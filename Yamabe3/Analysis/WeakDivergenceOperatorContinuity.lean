import Yamabe3.Analysis.WeakDivergenceSourceIdentity
import Yamabe3.Analysis.SobolevOperatorConvergence

/-! The actual variable-coefficient weak divergence operator is bounded
from H2 to L2 on each fixed precompact domain. The coefficient-dependent
constant precedes the input. No elliptic regularity estimate is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryLocalization
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
open Poincare.Analysis.Elliptic.Iteration
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_weakDivergenceSource_bound {O : Set E} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (a : E → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : E → ℝ, MemWkp 2 2 u O →
      MemWkp 0 2 (weakDivergenceSource O a u) O ∧
      iteratedWeakSobolevNorm 0 2 (weakDivergenceSource O a u) O ≤
        C * iteratedWeakSobolevNorm 2 2 u O := by
  classical
  choose A hA hbA using fun i j => exists_compact_sobolev_multiplier_bound 0 hO hOc
    (fun x => a x i j) (ha i j)
  choose B hB hbB using fun i j => exists_compact_sobolev_multiplier_bound 0 hO hOc
    (partialDeriv i (fun x => a x i j)) (contDiff_partial (ha i j) i)
  refine ⟨∑ i, ∑ j, (A i j+B i j), ENNReal.sum_ne_top.mpr (fun i _ =>
    ENNReal.sum_ne_top.mpr (fun j _ => ENNReal.add_ne_top.mpr ⟨hA i j,hB i j⟩)), ?_⟩
  intro u hu
  let p := fun j => chosenWeakPartial' 2 j u O
  let q := fun i j => chosenWeakPartial' 2 i (p j) O
  let G := fun i j x => a x i j*q i j x+partialDeriv i (fun y => a y i j) x*p j x
  have hp (j : Fin d) : MemWkp 1 2 (p j) O := hu.chosenWeakPartial_mem j
  have hq (i j : Fin d) : MemWkp 0 2 (q i j) O := (hp j).chosenWeakPartial_mem i
  have hG (i j : Fin d) : MemWkp 0 2 (G i j) O := MemWkp.add (by norm_num) hO
    (memWkp_mul_smooth_of_isCompact_closure 0 hO hOc (hq i j) (ha i j))
    (memWkp_mul_smooth_of_isCompact_closure 0 hO hOc (hp j).le_succ (contDiff_partial (ha i j) i))
  have hGn (i j : Fin d) : iteratedWeakSobolevNorm 0 2 (G i j) O ≤
      (A i j+B i j)*iteratedWeakSobolevNorm 2 2 u O := by
    calc
      _ ≤ iteratedWeakSobolevNorm 0 2 (fun x => a x i j*q i j x) O+
          iteratedWeakSobolevNorm 0 2 (fun x => partialDeriv i (fun y => a y i j) x*p j x) O :=
        wkpNorm_add_le (by norm_num) hO
          (memWkp_mul_smooth_of_isCompact_closure 0 hO hOc (hq i j) (ha i j))
          (memWkp_mul_smooth_of_isCompact_closure 0 hO hOc (hp j).le_succ (contDiff_partial (ha i j) i))
      _ ≤ A i j*iteratedWeakSobolevNorm 0 2 (q i j) O+B i j*iteratedWeakSobolevNorm 0 2 (p j) O :=
        add_le_add (hbA i j _ (hq i j)) (hbB i j _ (hp j).le_succ)
      _ ≤ A i j*iteratedWeakSobolevNorm 2 2 u O+B i j*iteratedWeakSobolevNorm 2 2 u O := by
        apply add_le_add
        · exact mul_le_mul le_rfl ((wkpNorm_chosenWeakPartial_le_wkpNorm_succ 0 2 (p j) O i).trans
            (wkpNorm_chosenWeakPartial_le_wkpNorm_succ 1 2 u O j)) zero_le zero_le
        · exact mul_le_mul le_rfl ((wkpNorm_mono_order (by norm_num : 0≤1) (p j) O).trans
            (wkpNorm_chosenWeakPartial_le_wkpNorm_succ 1 2 u O j)) zero_le zero_le
      _ = _ := (add_mul _ _ _).symm
  have hs := finite_sobolev_sum_with_bound hO 0 Finset.univ (fun i x => ∑ j, G i j x)
    (fun i _ => (finite_sobolev_sum_with_bound hO 0 Finset.univ (G i) (fun j _ => hG i j)).1)
  have hn := wkpNorm_const_smul (by norm_num : (1:ℝ≥0∞)≤2) hO hs.1 (-1)
  have hm := MemWkp.const_smul (by norm_num : (1:ℝ≥0∞)≤2) hO hs.1 (-1)
  simp only [neg_one_mul, enorm_neg, enorm_one, one_mul] at hn hm
  refine ⟨hm, hn.trans_le (hs.2.trans ?_)⟩
  calc
    _ ≤ ∑ i, ∑ j, iteratedWeakSobolevNorm 0 2 (G i j) O :=
      Finset.sum_le_sum (fun i _ => (finite_sobolev_sum_with_bound hO 0 Finset.univ (G i) (fun j _ => hG i j)).2)
    _ ≤ ∑ i, ∑ j, (A i j+B i j)*iteratedWeakSobolevNorm 2 2 u O :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hGn i j))
    _ = _ := by simp only [Finset.sum_mul]

theorem weakDivergenceSource_sub_ae {O : Set E} (hO : IsOpen O)
    (a : E → Matrix (Fin d) (Fin d) ℝ) {u v : E → ℝ}
    (hu : MemWkp 2 2 u O) (hv : MemWkp 2 2 v O) :
    weakDivergenceSource O a (fun x => u x-v x) =ᵐ[volume.restrict O]
      fun x => weakDivergenceSource O a u x-weakDivergenceSource O a v x := by
  have hp (j : Fin d) := iterWeakPartial_sub_two_ae hO (fun _ : Fin 1 => j) hu.le_succ hv.le_succ
  have hq (i j : Fin d) := iterWeakPartial_sub_two_ae hO ![j,i] hu hv
  filter_upwards [eventually_all.mpr hp, eventually_all.mpr (fun i => eventually_all.mpr (hq i))] with x hx hy
  change ∀ j, chosenWeakPartial' 2 j (fun x => u x-v x) O x=
    chosenWeakPartial' 2 j u O x-chosenWeakPartial' 2 j v O x at hx
  change ∀ i j, chosenWeakPartial' 2 i (chosenWeakPartial' 2 j (fun x => u x-v x) O) O x=
    chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u O) O x-
    chosenWeakPartial' 2 i (chosenWeakPartial' 2 j v O) O x at hy
  simp only [weakDivergenceSource, hx, hy, mul_sub]
  simp only [sub_add_sub_comm, Finset.sum_sub_distrib]
  ring

theorem exists_weakDivergenceSource_difference_bound {O : Set E} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (a : E → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u v : E → ℝ, MemWkp 2 2 u O → MemWkp 2 2 v O →
      iteratedWeakSobolevNorm 0 2 (fun x => weakDivergenceSource O a u x-weakDivergenceSource O a v x) O ≤
        C * iteratedWeakSobolevNorm 2 2 (fun x => u x-v x) O := by
  obtain ⟨C,hC,hb⟩ := exists_weakDivergenceSource_bound hO hOc a ha
  refine ⟨C,hC,?_⟩
  intro u v hu hv
  rw [← wkpNorm_congr_ae (k:=0) (by norm_num) hO (weakDivergenceSource_sub_ae hO a hu hv)]
  exact (hb _ (MemWkp.sub (by norm_num) hO hu hv)).2

#print axioms exists_weakDivergenceSource_bound
#print axioms weakDivergenceSource_sub_ae
#print axioms exists_weakDivergenceSource_difference_bound
end Yamabe3.Analysis.UniformElliptic
