/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Elliptic/Regularity/InteriorEstimates/Sobolev/HigherOrder.lean

Uses the nested-domain step of the higher-order induction and includes a bounded zeroth-
order term.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.UniformElliptic.UniformHigherOrder

/-!
# Uniform higher regularity with a genuine variable zeroth-order term

The source is f + q*u in the actual weak divergence equation. Nested-set
induction controls the lower-order product from the preceding regularity
level. There is no circular use of unknown solution jets and no assumed
right inverse. All constants precede the coefficient field, potential and
solution; only common finite jet bounds are used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A signed smooth variable potential with common finite jets preserves
uniform gain of two derivatives. The constant is chosen before B and q. -/
theorem exists_uniform_derivativeProfile_add_two_with_potential
    (k : ℕ) {Ω V W : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVΩ : closure V ⊆ Ω) (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hWV : closure W ⊆ V) {κ L Q : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : SmoothEllipticBilinearForm d Ω), κ ≤ B.lam →
      (∀ n ≤ k + 2, ∀ x ∈ V, ∀ i j : Fin d,
        ‖iteratedFDeriv ℝ n (fun y => B.a y i j) x‖ ≤ L) →
      (∀ x ∈ V, (∑ i : Fin d, ∑ j : Fin d,
        (B.a x i j - (1 : Matrix (Fin d) (Fin d) ℝ) i j) ^ 2) ≤ 1 / 4) →
      ∀ (q : E → ℝ), ContDiff ℝ ∞ q →
      (∀ n ≤ k, ∀ x ∈ V, ‖iteratedFDeriv ℝ n q x‖ ≤ Q) →
      ∀ {u f : E → ℝ}, ContDiff ℝ ∞ u → ContDiff ℝ ∞ f →
        WeakEquation V (matrixFlux B.a (fun j => partialDeriv j u))
          (fun x => f x + q x * u x) →
        derivativeProfile 2 W (k + 2) u ≤ ENNReal.ofReal C *
          (derivativeProfile 2 V 0 u + derivativeProfile 2 V k f) := by
  induction k generalizing V W with
  | zero =>
      obtain ⟨A, hA, hbound⟩ := exists_uniform_derivativeProfile_add_two_le_source
        0 hV hVc hVΩ hW hWc hWV hκ hL
      let D := cutoffMultiplier 0 Q
      have hD : 0 ≤ D := cutoffMultiplier_nonneg 0 hQ
      refine ⟨A * (1 + D), mul_nonneg hA (by positivity), ?_⟩
      intro B hB hjet hosc q hq hqjet u f hu hf heq
      have h := hbound B hB hjet hosc hu (hf.add (hq.mul hu)) heq
      have hm := derivativeProfile_mul_le hV (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        0 hq hu hQ hqjet
      have hs := derivativeProfile_add_le hV (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        0 hf (hq.mul hu)
      apply h.trans
      apply (mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (hs.trans (add_le_add le_rfl hm))) zero_le).trans
      rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_add zero_le_one hD, ENNReal.ofReal_one]
      let U := derivativeProfile 2 V 0 u
      let F := derivativeProfile 2 V 0 f
      change ENNReal.ofReal A * (U + (F + ENNReal.ofReal D * U)) ≤
        ENNReal.ofReal A * (1 + ENNReal.ofReal D) * (U + F)
      calc
        _ ≤ ENNReal.ofReal A * (U + (F + ENNReal.ofReal D * (U + F))) := by
          gcongr
          exact le_self_add
        _ = _ := by ring
  | succ k ih =>
      obtain ⟨U, hU, hWU, hUV⟩ := hWc.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hWV)
      have hUc : IsCompact (closure U) :=
        hVc.of_isClosed_subset isClosed_closure (hUV.trans subset_closure)
      have hUΩ : closure U ⊆ Ω := hUV.trans (subset_closure.trans hVΩ)
      obtain ⟨A, hA, hprior⟩ := ih hV hVc hVΩ hU hUc hUV
      obtain ⟨H, hH, hbound⟩ := exists_uniform_derivativeProfile_add_two_le_source
        (k + 1) hU hUc hUΩ hW hWc hWU hκ hL
      let D := cutoffMultiplier (k + 1) Q
      have hD : 0 ≤ D := cutoffMultiplier_nonneg (k + 1) hQ
      refine ⟨H * (A + 1 + D * A), mul_nonneg hH (by positivity), ?_⟩
      intro B hB hjet hosc q hq hqjet u f hu hf heq
      let T := derivativeProfile 2 V 0 u + derivativeProfile 2 V (k + 1) f
      have hjetV : ∀ n ≤ k + 2, ∀ x ∈ V, ∀ i j : Fin d,
          ‖iteratedFDeriv ℝ n (fun y => B.a y i j) x‖ ≤ L :=
        fun n hn x hx i j => hjet n (by omega) x hx i j
      have hqjetV : ∀ n ≤ k, ∀ x ∈ V, ‖iteratedFDeriv ℝ n q x‖ ≤ Q :=
        fun n hn x hx => hqjet n (by omega) x hx
      have hjetU : ∀ n ≤ k + 1 + 2, ∀ x ∈ U, ∀ i j : Fin d,
          ‖iteratedFDeriv ℝ n (fun y => B.a y i j) x‖ ≤ L :=
        fun n hn x hx i j => hjet n hn x (hUV (subset_closure hx)) i j
      have hqjetU : ∀ n ≤ k + 1, ∀ x ∈ U, ‖iteratedFDeriv ℝ n q x‖ ≤ Q :=
        fun n hn x hx => hqjet n hn x (hUV (subset_closure hx))
      have hoscU : ∀ x ∈ U, (∑ i : Fin d, ∑ j : Fin d,
          (B.a x i j - (1 : Matrix (Fin d) (Fin d) ℝ) i j) ^ 2) ≤ 1 / 4 :=
        fun x hx => hosc x (hUV (subset_closure hx))
      have huU : derivativeProfile 2 U (k + 2) u ≤ ENNReal.ofReal A * T := by
        apply (hprior B hB hjetV hosc q hq hqjetV hu hf heq).trans
        dsimp [T]
        gcongr
        exact derivativeProfile_mono_order (Nat.le_succ k) f
      have hu0 : derivativeProfile 2 U 0 u ≤ ENNReal.ofReal A * T :=
        (derivativeProfile_mono_order (by omega : 0 ≤ k + 2) u).trans huU
      have hu1 : derivativeProfile 2 U (k + 1) u ≤ ENNReal.ofReal A * T :=
        (derivativeProfile_mono_order (by omega : k + 1 ≤ k + 2) u).trans huU
      have hfU : derivativeProfile 2 U (k + 1) f ≤ T :=
        (derivativeProfile_mono_set (subset_closure.trans hUV) 2 (k + 1) f).trans le_add_self
      have hm := derivativeProfile_mul_le hU (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        (k + 1) hq hu hQ hqjetU
      have hprod : derivativeProfile 2 U (k + 1) (fun x => q x * u x) ≤
          ENNReal.ofReal D * (ENNReal.ofReal A * T) :=
        hm.trans (mul_le_mul_of_nonneg_left hu1 zero_le)
      have hsource := derivativeProfile_add_le hU (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        (k + 1) hf (hq.mul hu)
      have hs : derivativeProfile 2 U (k + 1) (fun x => f x + q x * u x) ≤
          T + ENNReal.ofReal D * (ENNReal.ofReal A * T) :=
        hsource.trans (add_le_add hfU hprod)
      have h := hbound B hB hjetU hoscU hu (hf.add (hq.mul hu))
        (heq.restrict (subset_closure.trans hUV))
      apply h.trans
      apply (mul_le_mul_of_nonneg_left (add_le_add hu0 hs) zero_le).trans_eq
      rw [ENNReal.ofReal_mul hH,
        ENNReal.ofReal_add (add_nonneg hA zero_le_one) (mul_nonneg hD hA),
        ENNReal.ofReal_add hA zero_le_one, ENNReal.ofReal_one,
        ENNReal.ofReal_mul hD]
      ring

#print axioms exists_uniform_derivativeProfile_add_two_with_potential

end Yamabe3.Analysis.UniformElliptic
