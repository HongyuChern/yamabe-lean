import Yamabe3.Analysis.SobolevNormLimits
import Yamabe3.Analysis.UniformElliptic.LocalProfileWeakNormComparison

/-! The literal negative weak Euclidean Laplacian is an H(k+2) to Hk
operator. Its norm continuity is proved for actual weak derivatives; it is
not supplied as an additional elliptic estimate assumption. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

def weakNegativeLaplacian (O : Set E) (u : E → ℝ) : E → ℝ :=
  fun x => -(∑ i : Fin d, iterWeakPartial 2 2 (fun _ => i) u O x)

theorem weak_second_mem_bound {O : Set E} (k : ℕ) {u : E → ℝ}
    (hu : MemWkp (k+2) 2 u O) (i : Fin d) :
    MemWkp k 2 (iterWeakPartial 2 2 (fun _ => i) u O) O ∧
      iteratedWeakSobolevNorm k 2 (iterWeakPartial 2 2 (fun _ => i) u O) O ≤
        iteratedWeakSobolevNorm (k+2) 2 u O := by
  have hp : MemWkp (k+1) 2 (chosenWeakPartial' 2 i u O) O := hu.chosenWeakPartial_mem i
  have hpp := hp.chosenWeakPartial_mem i
  have hn := (wkpNorm_chosenWeakPartial_le_wkpNorm_succ k 2 (chosenWeakPartial' 2 i u O) O i).trans
    (wkpNorm_chosenWeakPartial_le_wkpNorm_succ (k+1) 2 u O i)
  exact ⟨hpp,hn⟩

theorem weakNegativeLaplacian_mem_bound {O : Set E} (hO : IsOpen O)
    (k : ℕ) {u : E → ℝ} (hu : MemWkp (k+2) 2 u O) :
    MemWkp k 2 (weakNegativeLaplacian O u) O ∧
      iteratedWeakSobolevNorm k 2 (weakNegativeLaplacian O u) O ≤
        (d : ℝ≥0∞)*iteratedWeakSobolevNorm (k+2) 2 u O := by
  classical
  have hs := finite_sobolev_sum_with_bound hO k Finset.univ
    (fun i : Fin d => iterWeakPartial 2 2 (fun _ => i) u O)
    (fun i _ => (weak_second_mem_bound k hu i).1)
  have hm := MemWkp.const_smul (by norm_num : (1:ℝ≥0∞) ≤ 2) hO hs.1 (-1)
  have hn := wkpNorm_const_smul (by norm_num : (1:ℝ≥0∞) ≤ 2) hO hs.1 (-1)
  simp only [neg_one_mul, enorm_neg, enorm_one, one_mul] at hm hn
  refine ⟨hm, hn.trans_le (hs.2.trans ?_)⟩
  calc
    _ ≤ ∑ _ : Fin d, iteratedWeakSobolevNorm (k+2) 2 u O :=
      Finset.sum_le_sum (fun i _ => (weak_second_mem_bound k hu i).2)
    _ = _ := by simp [nsmul_eq_mul]

theorem weakNegativeLaplacian_sub_ae {O : Set E} (hO : IsOpen O)
    {u v : E → ℝ} (hu : MemWkp 2 2 u O) (hv : MemWkp 2 2 v O) :
    weakNegativeLaplacian O (fun x => u x-v x) =ᵐ[volume.restrict O]
      fun x => weakNegativeLaplacian O u x-weakNegativeLaplacian O v x := by
  filter_upwards [eventually_all.mpr (fun i : Fin d =>
    iterWeakPartial_sub_two_ae hO (fun _ : Fin 2 => i) hu hv)] with x hx
  simp only [weakNegativeLaplacian, hx, Finset.sum_sub_distrib]
  ring

theorem weakNegativeLaplacian_difference_bound {O : Set E} (hO : IsOpen O)
    (k : ℕ) {u v : E → ℝ} (hu : MemWkp (k+2) 2 u O) (hv : MemWkp (k+2) 2 v O) :
    iteratedWeakSobolevNorm k 2
      (fun x => weakNegativeLaplacian O u x-weakNegativeLaplacian O v x) O ≤
        (d : ℝ≥0∞)*iteratedWeakSobolevNorm (k+2) 2 (fun x => u x-v x) O := by
  rw [← wkpNorm_congr_ae (k := k) (by norm_num) hO
    (weakNegativeLaplacian_sub_ae hO (hu.le_of_le (by omega)) (hv.le_of_le (by omega)))]
  exact (weakNegativeLaplacian_mem_bound hO k (MemWkp.sub (by norm_num) hO hu hv)).2

theorem weakNegativeLaplacian_smooth_ae [NeZero d]
    {O : Set E} (hO : IsOpen O) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    weakNegativeLaplacian O u =ᵐ[volume.restrict O]
      principalSource (fun _ => (1 : Matrix (Fin d) (Fin d) ℝ)) u := by
  have hm : MemWkp 2 2 u univ := MemWkp_of_smooth_compactSupport
    isOpen_univ hu hc (subset_univ _) (by norm_num) 2
  have hj (i : Fin d) : iterWeakPartial 2 2 (fun _ => i) u O =ᵐ[volume.restrict O]
      iterClassicalPartial 2 (fun _ => i) u := by
    have hg := iterWeakPartial_smooth_ae_eq_iterClassicalPartial (by norm_num : (1:ℝ≥0∞) ≤ 2)
      isOpen_univ 2 (fun _ : Fin 2 => i) hu hc (subset_univ _)
    rw [Measure.restrict_univ] at hg
    exact (iterWeakPartial_mono_set_ae (by norm_num) hO (subset_univ _) (fun _ : Fin 2 => i) hm).symm.trans
      (ae_restrict_of_ae hg)
  filter_upwards [eventually_all.mpr hj] with x hx
  simp only [weakNegativeLaplacian, hx, principalSource]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hf : matrixFlux (fun _ => (1 : Matrix (Fin d) (Fin d) ℝ))
      (fun j => partialDeriv j u) i = partialDeriv i u := by
    funext y
    simp [matrixFlux, Matrix.one_apply]
  rw [hf]
  rfl

#print axioms weakNegativeLaplacian_mem_bound
#print axioms weakNegativeLaplacian_difference_bound
#print axioms weakNegativeLaplacian_smooth_ae
end Yamabe3.Analysis.UniformElliptic
