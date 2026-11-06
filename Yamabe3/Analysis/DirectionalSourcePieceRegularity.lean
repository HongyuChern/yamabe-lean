/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Sobolev/Boundary/Regularity/Normal.lean

Uses the finite-sum Sobolev argument in the source calculation on a directional piece.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.DirectionalPieceRecovery

/-! The explicit global differentiated source has H1 on each side once
the same solution has H3 there. Chosen derivatives on distinct domains
are identified almost everywhere before transferring Sobolev regularity. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryLocalization
open Poincare.Analysis.Elliptic.Iteration
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem piece_sobolev_sum {O : Set E} (hO : IsOpen O) (k : ℕ)
    {ι : Type*} (s : Finset ι) {v : ι → E → ℝ}
    (hv : ∀i∈s,MemWkp k 2 (v i) O) : MemWkp k 2 (fun x => ∑i∈s,v i x) O := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (MemWkp_zero_fun (d:=d) (k:=k) (by norm_num) hO)
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using MemWkp.add (by norm_num) hO
      (hv a (Finset.mem_insert_self a s)) (ih (fun i hi => hv i (Finset.mem_insert_of_mem hi)))

theorem memWkp_differentiatedSource_on_piece
    {W : Set E} (hW : IsOpen W) (hWc : IsCompact (closure W)) (m : ℕ)
    (A : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀i j,ContDiff ℝ ∞ (fun x => A x i j))
    {p : Fin d → E → ℝ} {q : Fin d → Fin d → E → ℝ} {r : E → ℝ}
    (hp : ∀j,MemWkp m 2 (p j) W) (hq : ∀i j,MemWkp m 2 (q i j) W)
    (hr : MemWkp m 2 r W) (k : Fin d) :
    MemWkp m 2 (differentiatedSource A p q r k) W := by
  apply MemWkp.add (by norm_num) hW hr
  apply piece_sobolev_sum hW m Finset.univ
  intro i _
  apply piece_sobolev_sum hW m Finset.univ
  intro j _
  exact MemWkp.add (by norm_num) hW
    (memWkp_mul_smooth_of_isCompact_closure m hW hWc (hq i j) (contDiff_partial (hA i j) k))
    (memWkp_mul_smooth_of_isCompact_closure m hW hWc (hp j)
      (contDiff_partial (contDiff_partial (hA i j) k) i))

theorem explicit_directional_source_H1_on_piece
    {O W : Set E} (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWO : W⊆O)
    (A : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀i j,ContDiff ℝ ∞ (fun x => A x i j))
    {u f r : E → ℝ} (hu : MemWkp 2 2 u O) (huW : MemWkp 3 2 u W)
    (hfW : MemWkp 2 2 f W) (hr : MemLp r 2 (volume.restrict O))
    (k : Fin d) (hfr : HasWeakPartialDeriv k r f O) :
    MemWkp 1 2
      (differentiatedSource A (fun j => chosenWeakPartial' 2 j u O)
        (fun i j => chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u O) O) r k) W := by
  have h1 (j : Fin d) := chosenWeakPartial'_mono_set_ae (by norm_num : (1:ℝ≥0∞)≤2) hW hWO hu.memW1p j
  have h2 (i j : Fin d) :=
    (chosenWeakPartial'_mono_set_ae (by norm_num : (1:ℝ≥0∞)≤2) hW hWO
      (hu.chosenWeakPartial_mem i).memW1p j).trans
      (chosenWeakPartial'_ae_congr (by norm_num) hW (h1 i) j)
  have hp (j : Fin d) : MemWkp 1 2 (chosenWeakPartial' 2 j u O) W :=
    (MemWkp_congr_ae (by norm_num) hW (h1 j).symm).mp (huW.chosenWeakPartial_mem j).le_succ
  have hq (i j : Fin d) : MemWkp 1 2 (chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u O) O) W :=
    (MemWkp_congr_ae (by norm_num) hW (h2 i j).symm).mp
      ((huW.chosenWeakPartial_mem i).chosenWeakPartial_mem j)
  have hrW : MemLp r 2 (volume.restrict W) := hr.mono_measure (Measure.restrict_mono hWO le_rfl)
  have hre : r=ᵐ[volume.restrict W] chosenWeakPartial' 2 k f W :=
    HasWeakPartialDeriv.ae_eq hW (hfr.restrict hW hWO)
      (chosenWeakPartial'_isWeakPartial_of_mem hfW.memW1p k)
      (hrW.locallyIntegrable (by norm_num))
      ((chosenWeakPartial'_memLp_of_mem hfW.memW1p k).locallyIntegrable (by norm_num))
  have hr1 : MemWkp 1 2 r W := (MemWkp_congr_ae (by norm_num) hW hre.symm).mp
    (hfW.chosenWeakPartial_mem k)
  exact memWkp_differentiatedSource_on_piece hW hWc 1 A hA hp hq hr1 k

#print axioms memWkp_differentiatedSource_on_piece
#print axioms explicit_directional_source_H1_on_piece
end Yamabe3.Analysis.UniformElliptic
