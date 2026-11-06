/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Sobolev/Boundary/Regularity/Normal.lean

Retains the finite-sum Sobolev argument as a private helper for the differentiated
source.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import PoincareLib.Analysis.Sobolev.Boundary.DifferentiatedEquation
import PoincareLib.Analysis.Sobolev.Boundary.Localization.Sobolev

/-!
# Actual Sobolev regularity of the differentiated elliptic source

The commutator source is constructed from the existing weak derivatives,
not supplied as a new regularity premise. This is a local auxiliary result;
it supplies neither a boundary estimate nor a norm bound.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryTangential
open Poincare.Analysis.Sobolev.BoundaryLocalization
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem finite_sobolev_sum {O : Set E} (hO : IsOpen O) (k : ℕ)
    {ι : Type*} (s : Finset ι) {v : ι → E → ℝ}
    (hv : ∀ i ∈ s, MemWkp k 2 (v i) O) :
    MemWkp k 2 (fun x => ∑ i ∈ s, v i x) O := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (MemWkp_zero_fun (d := d) (k := k) (by norm_num) hO)
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      MemWkp.add (by norm_num) hO (hv a (Finset.mem_insert_self a s))
        (ih (fun i hi => hv i (Finset.mem_insert_of_mem hi)))

/-- The differentiated PDE has a genuine H^k source, including every
coefficient commutator, whenever u is H^(k+2) and its source is H^(k+1). -/
theorem exists_differentiated_sobolev_source
    (k : ℕ) {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (a : E → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    {u f : E → ℝ} (hu : MemWkp (k + 2) 2 u O) (hf : MemWkp (k + 1) 2 f O)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, a x i j * chosenWeakPartial' 2 j u O x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x)
    (l : Fin d) :
    ∃ F : E → ℝ, MemWkp k 2 F O ∧
      ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
        (∫ x in O, ∑ i, ∑ j, a x i j *
          chosenWeakPartial' 2 j (chosenWeakPartial' 2 l u O) O x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, F x * φ x := by
  let p (j : Fin d) := chosenWeakPartial' 2 j u O
  let q (i j : Fin d) := chosenWeakPartial' 2 j (p i) O
  let r := chosenWeakPartial' 2 l f O
  let da (i j : Fin d) (x : E) :=
    fderiv ℝ (fun y => a y i j) x (EuclideanSpace.single l 1)
  let dda (i j : Fin d) (x : E) := fderiv ℝ (da i j) x (EuclideanSpace.single i 1)
  let F : E → ℝ := fun x => r x + ∑ i, ∑ j, (dda i j x * p j x + da i j x * q i j x)
  have hp (i : Fin d) : MemWkp (k + 1) 2 (p i) O := hu.chosenWeakPartial_mem i
  have hq (i j : Fin d) : MemWkp k 2 (q i j) O := (hp i).chosenWeakPartial_mem j
  have hda (i j : Fin d) : ContDiff ℝ ∞ (da i j) :=
    ((ha i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdda (i j : Fin d) : ContDiff ℝ ∞ (dda i j) :=
    ((hda i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hF : MemWkp k 2 F O :=
    MemWkp.add (by norm_num) hO (hf.chosenWeakPartial_mem l)
      (finite_sobolev_sum hO k _ fun i _ => finite_sobolev_sum hO k _ fun j _ =>
        MemWkp.add (by norm_num) hO
          (memWkp_mul_smooth_of_isCompact_closure k hO hOc (hp j).le_succ (hdda i j))
          (memWkp_mul_smooth_of_isCompact_closure k hO hOc (hq i j) (hda i j)))
  have hw (i j : Fin d) : HasWeakPartialDeriv i (q i j) (p j) O :=
    weakPartial_commute i j
      (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i)
      (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p j)
      (chosenWeakPartial'_isWeakPartial_of_mem (hp i).memW1p j)
  have h := differentiated_weak_divergence hO hOc a ha l
    (fun i => (hp i).memLp) (fun i j => (hq i j).memLp) hw
    hf.memLp (hf.chosenWeakPartial_mem l).memLp
    (chosenWeakPartial'_isWeakPartial_of_mem hf.memW1p l) heq
  exact ⟨F, hF, h.2⟩

#print axioms exists_differentiated_sobolev_source
end Yamabe3.Analysis.UniformElliptic

