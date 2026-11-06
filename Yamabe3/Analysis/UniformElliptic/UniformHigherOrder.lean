/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Elliptic/Regularity/InteriorEstimates/Sobolev/HigherOrder.lean

Adapts the differentiated equation and higher-order induction to constants fixed over a
coefficient family.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.UniformElliptic.UniformH2Profile
import Yamabe3.Analysis.UniformElliptic.UniformCommutator

/-!
# Uniform higher-order estimates before the coefficient field

The base H2 estimate is the proved explicit near-identity perturbation bound.
Differentiating the genuine weak equation uses the same coefficients; all
commutator constants depend only on common finite jet bounds and fixed sets.
The induction follows pinned Sobolev/HigherOrder at commit
62db01af9388dc1d9b56b66d6674f4c09b2318a2 (Apache-2.0), with each
coefficient-dependent choice replaced by a proved family-uniform estimate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem smooth_differentiatedSource
    (A : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    {u f : E → ℝ} (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f) (k : Fin d) :
    ContDiff ℝ ∞ (differentiatedSource A (fun j => partialDeriv j u)
      (fun i j => partialDeriv i (partialDeriv j u)) (partialDeriv k f) k) := by
  apply ContDiff.add (contDiff_partial hf k)
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  exact ((contDiff_partial (hA i j) k).mul (contDiff_partial (contDiff_partial hu j) i)).add
    ((contDiff_partial (contDiff_partial (hA i j) k) i).mul (contDiff_partial hu j))

omit [NeZero d] in
private theorem weakEquation_partial {V : Set E} (hV : IsOpen V)
    (A : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    {u f : E → ℝ} (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (heq : WeakEquation V (matrixFlux A (fun j => partialDeriv j u)) f) (k : Fin d) :
    WeakEquation V (matrixFlux A (fun j => partialDeriv j (partialDeriv k u)))
      (differentiatedSource A (fun j => partialDeriv j u)
        (fun i j => partialDeriv i (partialDeriv j u)) (partialDeriv k f) k) := by
  have hlocal {v : E → ℝ} (hv : Continuous v) : LocallyIntegrable v (volume.restrict V) :=
    hv.locallyIntegrable.mono_measure Measure.restrict_le_self
  have hdiff := differentiated_equation hV k hA
    (fun j => hlocal (contDiff_partial hu j).continuous)
    (fun i j => hlocal (contDiff_partial (contDiff_partial hu j) i).continuous)
    (hlocal (contDiff_partial hf k).continuous)
    (fun i j => HasWeakPartialDeriv.of_contDiff (i := i) hV
      ((contDiff_partial hu j).of_le (by simp)))
    (HasWeakPartialDeriv.of_contDiff (i := k) hV (hf.of_le (by simp))) heq
  apply hdiff.congr_flux
  intro i
  exact Eventually.of_forall fun x => by
    unfold matrixFlux
    apply Finset.sum_congr rfl
    intro j hj
    change A x i j * partialDeriv k (partialDeriv j u) x =
      A x i j * partialDeriv j (partialDeriv k u) x
    exact congrArg (fun v : E → ℝ => A x i j * v x) (partial_comm hu k j)

/-- A common ellipticity lower bound, a common finite coefficient jet bound
and a fixed near-identity bound give one H^(k+2) estimate for all coefficient
fields. The constant precedes the coefficients and both functions. -/
theorem exists_uniform_derivativeProfile_add_two_le_source
    (k : ℕ) {Ω V W : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVΩ : closure V ⊆ Ω) (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hWV : closure W ⊆ V) {κ L : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : SmoothEllipticBilinearForm d Ω), κ ≤ B.lam →
      (∀ n ≤ k + 2, ∀ x ∈ V, ∀ i j : Fin d,
        ‖iteratedFDeriv ℝ n (fun y => B.a y i j) x‖ ≤ L) →
      (∀ x ∈ V, (∑ i : Fin d, ∑ j : Fin d,
        (B.a x i j - (1 : Matrix (Fin d) (Fin d) ℝ) i j) ^ 2) ≤ 1 / 4) →
      ∀ {u f : E → ℝ}, ContDiff ℝ ∞ u → ContDiff ℝ ∞ f →
        WeakEquation V (matrixFlux B.a (fun j => partialDeriv j u)) f →
        derivativeProfile 2 W (k + 2) u ≤ ENNReal.ofReal C *
          (derivativeProfile 2 V 0 u + derivativeProfile 2 V k f) := by
  induction k generalizing V W with
  | zero =>
      obtain ⟨C, hC, hbound⟩ := exists_uniform_derivativeProfile_two_le_source
        hV hVc hVΩ hW hWc hWV hκ hL hL
      refine ⟨C, hC, ?_⟩
      intro B hB hjet hosc u f hu hf heq
      apply hbound B hB ?_ ?_ hosc hu hf heq
      · intro x hx i j
        simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
          hjet 0 (by omega) x hx i j
      · intro x hx i j
        have h := norm_iteratedFDeriv_partial_le (B.smooth_a i j) i 0 x
        rw [norm_iteratedFDeriv_zero] at h
        exact h.trans (hjet 1 (by omega) x hx i j)
  | succ k ih =>
      obtain ⟨U, hU, hWU, hUV⟩ := hWc.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hWV)
      have hUc : IsCompact (closure U) :=
        hVc.of_isClosed_subset isClosed_closure (hUV.trans subset_closure)
      have hUΩ : closure U ⊆ Ω := hUV.trans (subset_closure.trans hVΩ)
      obtain ⟨A, hA, hprior⟩ := ih hV hVc hVΩ hU hUc hUV
      obtain ⟨H, hH, hpartial⟩ := ih hU hUc hUΩ hW hWc hWU
      obtain ⟨D0, hD0, hcomm⟩ := exists_uniform_differentiatedSource_profile_le hU k hL
      let D : Fin d → ℝ := fun _ => D0
      have hD (i : Fin d) : 0 ≤ D i := hD0
      let coeff : Fin d → ℝ := fun i => H * (A + D i * (A + 1))
      have hcoeff (i : Fin d) : 0 ≤ coeff i :=
        mul_nonneg hH (add_nonneg hA (mul_nonneg (hD i) (add_nonneg hA zero_le_one)))
      let C : ℝ := 1 + ∑ i, coeff i
      refine ⟨C, add_nonneg zero_le_one (Finset.sum_nonneg (fun i _ => hcoeff i)), ?_⟩
      intro B hB hjet hosc u f hu hf heq
      have hjetV : ∀ n ≤ k + 2, ∀ x ∈ V, ∀ i j : Fin d,
          ‖iteratedFDeriv ℝ n (fun y => B.a y i j) x‖ ≤ L :=
        fun n hn x hx i j => hjet n (by omega) x hx i j
      have hjetU : ∀ n ≤ k + 2, ∀ x ∈ U, ∀ i j : Fin d,
          ‖iteratedFDeriv ℝ n (fun y => B.a y i j) x‖ ≤ L :=
        fun n hn x hx i j => hjetV n hn x (hUV (subset_closure hx)) i j
      have hoscU : ∀ x ∈ U, (∑ i : Fin d, ∑ j : Fin d,
          (B.a x i j - (1 : Matrix (Fin d) (Fin d) ℝ) i j) ^ 2) ≤ 1 / 4 :=
        fun x hx => hosc x (hUV (subset_closure hx))
      let T := derivativeProfile 2 V 0 u + derivativeProfile 2 V (k + 1) f
      let source : Fin d → E → ℝ := fun i =>
        differentiatedSource B.a (fun j => partialDeriv j u)
          (fun a b => partialDeriv a (partialDeriv b u)) (partialDeriv i f) i
      have heqU := heq.restrict (subset_closure.trans hUV)
      have huU : derivativeProfile 2 U (k + 2) u ≤ ENNReal.ofReal A * T := by
        apply (hprior B hB hjetV hosc hu hf heq).trans
        dsimp [T]
        gcongr
        exact derivativeProfile_mono_order (Nat.le_succ k) f
      have hfU : derivativeProfile 2 U (k + 1) f ≤ T :=
        (derivativeProfile_mono_set (subset_closure.trans hUV) 2 (k + 1) f).trans le_add_self
      have hpart0 (i : Fin d) : derivativeProfile 2 U 0 (partialDeriv i u) ≤
          ENNReal.ofReal A * T :=
        ((derivativeProfile_partial_le 0 i hu).trans
          (derivativeProfile_mono_order (by omega : 1 ≤ k + 2) u)).trans huU
      have hsource (i : Fin d) : derivativeProfile 2 U k (source i) ≤
          ENNReal.ofReal (D i * (A + 1)) * T := by
        apply (hcomm B.a B.smooth_a hjetU i hu hf).trans
        calc
          ENNReal.ofReal (D i) *
              (derivativeProfile 2 U (k + 2) u + derivativeProfile 2 U (k + 1) f) ≤
              ENNReal.ofReal (D i) * (ENNReal.ofReal A * T + T) := by gcongr
          _ = ENNReal.ofReal (D i * (A + 1)) * T := by
            rw [ENNReal.ofReal_mul (hD i), ENNReal.ofReal_add hA zero_le_one,
              ENNReal.ofReal_one]
            ring
      have hpart (i : Fin d) : derivativeProfile 2 W (k + 2) (partialDeriv i u) ≤
          ENNReal.ofReal (coeff i) * T := by
        have h := hpartial B hB hjetU hoscU (contDiff_partial hu i)
          (smooth_differentiatedSource B.a B.smooth_a hu hf i)
          (weakEquation_partial hU B.a B.smooth_a hu hf heqU i)
        apply h.trans
        calc
          ENNReal.ofReal H *
              (derivativeProfile 2 U 0 (partialDeriv i u) + derivativeProfile 2 U k (source i)) ≤
              ENNReal.ofReal H *
                (ENNReal.ofReal A * T + ENNReal.ofReal (D i * (A + 1)) * T) := by
                  exact mul_le_mul_of_nonneg_left (add_le_add (hpart0 i) (hsource i)) zero_le
          _ = ENNReal.ofReal (coeff i) * T := by
            dsimp [coeff]
            rw [ENNReal.ofReal_mul hH,
              ENNReal.ofReal_add hA (mul_nonneg (hD i) (by positivity))]
            ring
      have hu0 : derivativeProfile 2 W 0 u ≤ T :=
        (derivativeProfile_mono_set (subset_closure.trans hWV) 2 0 u).trans le_self_add
      have hreconstruct := derivativeProfile_succ_le_sum_partial
        (Ω := W) (by norm_num : (1 : ℝ≥0∞) ≤ 2) (k + 2) hu
      have horder : k + 1 + 2 = k + 2 + 1 := by omega
      rw [horder]
      apply hreconstruct.trans
      apply (add_le_add hu0 (Finset.sum_le_sum (fun i hi => hpart i))).trans_eq
      dsimp [C]
      rw [ENNReal.ofReal_add zero_le_one (Finset.sum_nonneg (fun i hi => hcoeff i)),
        ENNReal.ofReal_one, ENNReal.ofReal_sum_of_nonneg (fun i hi => hcoeff i),
        add_mul, one_mul, Finset.sum_mul]

#print axioms exists_uniform_derivativeProfile_add_two_le_source

end Yamabe3.Analysis.UniformElliptic
