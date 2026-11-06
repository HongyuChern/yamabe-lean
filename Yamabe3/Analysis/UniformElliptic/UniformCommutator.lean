/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Elliptic/Regularity/InteriorEstimates/Operators/Commutator.lean

Adapts the differentiated source calculation to a commutator bound controlled by common
coefficient jets.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import PoincareLib.Analysis.Elliptic.Regularity.InteriorEstimates.Operators.Commutator

/-!
# Uniform commutator control from common coefficient jets

The constant is chosen before the coefficient field. Fixed explicit Leibniz
multipliers replace all coefficient-dependent compactness choices.
The algebraic source estimate is adapted from pinned Operators/Commutator,
commit 62db01af9388dc1d9b56b66d6674f4c09b2318a2 (Apache-2.0).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates
open Poincare.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- One commutator bound for all smooth coefficient fields with the same
jet bound through order r+2. It is independent of A, u, f and the direction. -/
theorem exists_uniform_differentiatedSource_profile_le
    {V : Set E} (hV : IsOpen V) (r : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : E → Matrix (Fin d) (Fin d) ℝ)
      (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j)),
      (∀ n ≤ r + 2, ∀ x ∈ V, ∀ i j : Fin d,
        ‖iteratedFDeriv ℝ n (fun y => A y i j) x‖ ≤ L) →
      ∀ (k : Fin d) {u f : E → ℝ}, ContDiff ℝ ∞ u → ContDiff ℝ ∞ f →
        derivativeProfile 2 V r
          (differentiatedSource A (fun j => partialDeriv j u)
            (fun i j => partialDeriv i (partialDeriv j u)) (partialDeriv k f) k) ≤
          ENNReal.ofReal C *
            (derivativeProfile 2 V (r + 2) u + derivativeProfile 2 V (r + 1) f) := by
  classical
  let Z := cutoffMultiplier r L
  let C : Fin d → Fin d → ℝ := fun _ _ => Z
  let D : Fin d → Fin d → ℝ := fun _ _ => Z
  have hC (i j : Fin d) : 0 ≤ C i j := cutoffMultiplier_nonneg r hL
  have hD (i j : Fin d) : 0 ≤ D i j := cutoffMultiplier_nonneg r hL
  let S : ℝ := ∑ i, ∑ j, (C i j + D i j)
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => add_nonneg (hC i j) (hD i j)
  refine ⟨1 + S, by positivity, ?_⟩
  intro A hA hjet k u f hu hf
  have hboundC (i j : Fin d) {p : ℝ≥0∞} (hp : 1 ≤ p)
      {v : E → ℝ} (hv : ContDiff ℝ ∞ v) :
      derivativeProfile p V r (fun x => partialDeriv k (fun y => A y i j) x * v x) ≤
        ENNReal.ofReal (C i j) * derivativeProfile p V r v := by
    apply derivativeProfile_mul_le hV hp r (contDiff_partial (hA i j) k) hv hL
    intro n hn x hx
    exact (norm_iteratedFDeriv_partial_le (hA i j) k n x).trans
      (hjet (n + 1) (by omega) x hx i j)
  have hboundD (i j : Fin d) {p : ℝ≥0∞} (hp : 1 ≤ p)
      {v : E → ℝ} (hv : ContDiff ℝ ∞ v) :
      derivativeProfile p V r
        (fun x => partialDeriv i (partialDeriv k (fun y => A y i j)) x * v x) ≤
        ENNReal.ofReal (D i j) * derivativeProfile p V r v := by
    apply derivativeProfile_mul_le hV hp r
      (contDiff_partial (contDiff_partial (hA i j) k) i) hv hL
    intro n hn x hx
    exact ((norm_iteratedFDeriv_partial_le (contDiff_partial (hA i j) k) i n x).trans
      (norm_iteratedFDeriv_partial_le (hA i j) k (n + 1) x)).trans
        (hjet (n + 1 + 1) (by omega) x hx i j)
  let U := derivativeProfile 2 V (r + 2) u
  let F := derivativeProfile 2 V (r + 1) f
  let term : Fin d → Fin d → E → ℝ := fun i j x =>
    partialDeriv k (fun y => A y i j) x *
        partialDeriv i (partialDeriv j u) x +
      partialDeriv i (partialDeriv k (fun y => A y i j)) x *
        partialDeriv j u x
  have hterm (i j) : ContDiff ℝ (⊤ : ℕ∞) (term i j) :=
    ((contDiff_partial (hA i j) k).mul (contDiff_partial (contDiff_partial hu j) i)).add
      ((contDiff_partial (contDiff_partial (hA i j) k) i).mul (contDiff_partial hu j))
  have htermBound (i j) : derivativeProfile 2 V r (term i j) ≤
      ENNReal.ofReal (C i j + D i j) * U := by
    have hfirst := hboundC i j (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (contDiff_partial (contDiff_partial hu j) i)
    have hsecond := hboundD i j (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (contDiff_partial hu j)
    have hdu : derivativeProfile 2 V r (partialDeriv j u) ≤ U :=
      (derivativeProfile_partial_le r j hu).trans
        (derivativeProfile_mono_order (Nat.le_succ (r + 1)) u)
    have hddu : derivativeProfile 2 V r
        (partialDeriv i (partialDeriv j u)) ≤ U :=
      (derivativeProfile_partial_le r i (contDiff_partial hu j)).trans
        (derivativeProfile_partial_le (r + 1) j hu)
    calc
      derivativeProfile 2 V r (term i j) ≤
          derivativeProfile 2 V r (fun x => partialDeriv k (fun y => A y i j) x *
            partialDeriv i (partialDeriv j u) x) +
          derivativeProfile 2 V r (fun x =>
            partialDeriv i (partialDeriv k (fun y => A y i j)) x *
              partialDeriv j u x) :=
        derivativeProfile_add_le hV (by norm_num) r
          ((contDiff_partial (hA i j) k).mul (contDiff_partial (contDiff_partial hu j) i))
          ((contDiff_partial (contDiff_partial (hA i j) k) i).mul (contDiff_partial hu j))
      _ ≤ ENNReal.ofReal (C i j) * U + ENNReal.ofReal (D i j) * U := by
        gcongr
        · exact hfirst.trans (by gcongr)
        · exact hsecond.trans (by gcongr)
      _ = ENNReal.ofReal (C i j + D i j) * U := by
        rw [ENNReal.ofReal_add (hC i j) (hD i j), add_mul]
  have hsum : derivativeProfile 2 V r (fun x => ∑ i, ∑ j, term i j x) ≤
      ENNReal.ofReal S * U := by
    apply (derivativeProfile_finset_sum_le hV (by norm_num) r Finset.univ
      (fun i hi => ContDiff.sum (fun j hj => hterm i j))).trans
    change (∑ i, derivativeProfile 2 V r (fun x => ∑ j, term i j x)) ≤
      ENNReal.ofReal (∑ i, ∑ j, (C i j + D i j)) * U
    rw [ENNReal.ofReal_sum_of_nonneg
      (fun i hi => Finset.sum_nonneg fun j hj => add_nonneg (hC i j) (hD i j)),
      Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    apply (derivativeProfile_finset_sum_le hV (by norm_num) r Finset.univ
      (fun j hj => hterm i j)).trans
    rw [ENNReal.ofReal_sum_of_nonneg (fun j hj => add_nonneg (hC i j) (hD i j)),
      Finset.sum_mul]
    exact Finset.sum_le_sum fun j hj => htermBound i j
  have hsmoothSum : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ i, ∑ j, term i j x) :=
    ContDiff.sum (fun i hi => ContDiff.sum (fun j hj => hterm i j))
  have hsource := derivativeProfile_add_le hV (by norm_num : (1 : ℝ≥0∞) ≤ 2) r
    (contDiff_partial hf k)
    hsmoothSum
  change derivativeProfile 2 V r (fun x => partialDeriv k f x +
    ∑ i, ∑ j, term i j x) ≤ _
  apply hsource.trans
  apply (add_le_add (derivativeProfile_partial_le r k hf) hsum).trans
  rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hS, ENNReal.ofReal_one]
  calc
    F + ENNReal.ofReal S * U ≤ (1 + ENNReal.ofReal S) * F +
        (1 + ENNReal.ofReal S) * U := by
      apply add_le_add
      · calc
          F = 1 * F := (one_mul F).symm
          _ ≤ (1 + ENNReal.ofReal S) * F := by gcongr; exact le_self_add
      · gcongr; exact le_add_self
    _ = (1 + ENNReal.ofReal S) * (U + F) := by ring

#print axioms exists_uniform_differentiatedSource_profile_le

end Yamabe3.Analysis.UniformElliptic
