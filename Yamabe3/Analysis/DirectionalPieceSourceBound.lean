import Yamabe3.Analysis.WeakDivergenceHigherOrderBound
import Yamabe3.Analysis.DirectionalSourcePieceRegularity

/-! Bound the actual globally differentiated source on one piece after
identifying its chosen derivatives in that same restricted measure. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
open Poincare.Analysis.Elliptic.Iteration
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem explicit_directional_source_restrict_ae
    {O W : Set E} (hW : IsOpen W) (hWO : W⊆O)
    (a : E → Matrix (Fin d) (Fin d) ℝ) {u f r : E → ℝ}
    (hu : MemWkp 2 2 u O) (hfW : MemWkp 2 2 f W)
    (hr : MemLp r 2 (volume.restrict O)) (k : Fin d) (hfr : HasWeakPartialDeriv k r f O) :
    differentiatedSource a (fun j => chosenWeakPartial' 2 j u O)
      (fun i j => chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u O) O) r k =ᵐ[volume.restrict W]
    differentiatedSource a (fun j => chosenWeakPartial' 2 j u W)
      (fun i j => chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u W) W)
      (chosenWeakPartial' 2 k f W) k := by
  have h1 (j : Fin d) := chosenWeakPartial'_mono_set_ae (by norm_num : (1:ℝ≥0∞)≤2) hW hWO hu.memW1p j
  have h2 (i j : Fin d) :=
    (chosenWeakPartial'_mono_set_ae (by norm_num : (1:ℝ≥0∞)≤2) hW hWO
      (hu.chosenWeakPartial_mem i).memW1p j).trans
      (chosenWeakPartial'_ae_congr (by norm_num) hW (h1 i) j)
  have hre : r=ᵐ[volume.restrict W] chosenWeakPartial' 2 k f W :=
    HasWeakPartialDeriv.ae_eq hW (hfr.restrict hW hWO)
      (chosenWeakPartial'_isWeakPartial_of_mem hfW.memW1p k)
      ((hr.mono_measure (Measure.restrict_mono hWO le_rfl)).locallyIntegrable (by norm_num))
      ((chosenWeakPartial'_memLp_of_mem hfW.memW1p k).locallyIntegrable (by norm_num))
  filter_upwards [hre,eventually_all.mpr h1,eventually_all.mpr (fun i => eventually_all.mpr (h2 i))] with x hx hp hq
  simp only [differentiatedSource,hx,hp,hq]

theorem exists_explicit_directional_piece_H1_bound
    {W : Set E} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (a : E → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j,ContDiff ℝ ∞ (fun x => a x i j)) (k : Fin d) :
    ∃ C : ℝ≥0∞, C≠⊤ ∧ ∀ {O : Set E}, W⊆O → ∀ u f r : E → ℝ,
      MemWkp 2 2 u O → MemWkp 3 2 u W → MemWkp 2 2 f W →
      MemLp r 2 (volume.restrict O) → HasWeakPartialDeriv k r f O →
      iteratedWeakSobolevNorm 1 2
        (differentiatedSource a (fun j => chosenWeakPartial' 2 j u O)
          (fun i j => chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u O) O) r k) W ≤
        iteratedWeakSobolevNorm 2 2 f W+C*iteratedWeakSobolevNorm 3 2 u W := by
  let da : E → Matrix (Fin d) (Fin d) ℝ := fun x i j => partialDeriv k (fun y => a y i j) x
  obtain ⟨C,hC,hb⟩ := exists_weakDivergenceSource_bound_order 1 hW hWc da
    (fun i j => contDiff_partial (ha i j) k)
  refine ⟨C,hC,?_⟩
  intro O hWO u f r hu huW hfW hr hfr
  have he := (explicit_directional_source_restrict_ae hW hWO a hu hfW hr k hfr).trans
    (differentiatedSource_eq_weak_commutator_ae hW a k huW.le_succ (chosenWeakPartial' 2 k f W))
  rw [wkpNorm_congr_ae (k:=1) (by norm_num : (1:ℝ≥0∞)≤2) hW he]
  exact (sobolevNorm_sub_le hW (hfW.chosenWeakPartial_mem k) (hb u huW).1).trans
    (add_le_add (wkpNorm_chosenWeakPartial_le_wkpNorm_succ 1 2 f W k) (hb u huW).2)

#print axioms explicit_directional_source_restrict_ae
#print axioms exists_explicit_directional_piece_H1_bound
end Yamabe3.Analysis.UniformElliptic
