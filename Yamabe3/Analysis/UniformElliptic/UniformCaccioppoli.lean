/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Elliptic/Regularity/InteriorEstimates/Energy/Caccioppoli.lean

Retains the cutoff identity and energy estimate and bounds the cutoff term uniformly in
the coefficient field.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import PoincareLib.Analysis.Elliptic.Regularity.InteriorEstimates.Energy.Caccioppoli

/-!
# A Caccioppoli constant chosen before the coefficient field

The fixed upstream cutoff-energy proof is reused with an explicit bound for
its coefficient-dependent cutoff term. A common ellipticity lower bound and
entry bound now give one constant for all coefficient fields on fixed nested
sets. No compactness of arbitrary choice values is asserted.

The cutoff identity and energy proof are adapted from the pinned PoincareLib
`Analysis/Elliptic/Regularity/InteriorEstimates/Energy/Caccioppoli.lean`
at commit 62db01af9388dc1d9b56b66d6674f4c09b2318a2 (Apache-2.0).
The upstream source is unchanged.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The cutoff energy has a bound depending on the supplied coefficient
entry bound and the fixed cutoff derivative, with no choice over B. -/
theorem abs_principal_cutoff_le_of_entry_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) {η : E → ℝ}
    {A N : ℝ} (hA : 0 ≤ A) (hN : 0 ≤ N)
    (ha : ∀ x ∈ tsupport η, ∀ i j : Fin d, |B.a x i j| ≤ A)
    (hDη : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N) (x : E) :
    |B.principalIntegrand η η x| ≤ (d : ℝ) ^ 2 * A * N ^ 2 := by
  by_cases hx : x ∈ tsupport η
  · have hd (i : Fin d) : |fderiv ℝ η x (EuclideanSpace.single i 1)| ≤ N := by
      have h := (fderiv ℝ η x).le_opNorm (EuclideanSpace.single i 1)
      simpa only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one]
        using h.trans (by simpa using hDη x)
    unfold SmoothEllipticBilinearForm.principalIntegrand
    calc
      _ ≤ ∑ i : Fin d, ∑ j : Fin d,
          |B.a x i j * fderiv ℝ η x (EuclideanSpace.single i 1) *
            fderiv ℝ η x (EuclideanSpace.single j 1)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, A * N * N := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_mul]
        exact mul_le_mul
          (mul_le_mul (ha x hx i j) (hd i) (abs_nonneg _) hA)
          (hd j) (abs_nonneg _) (mul_nonneg hA hN)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  · simp [SmoothEllipticBilinearForm.principalIntegrand, fderiv_of_notMem_tsupport ℝ hx]
    positivity

/-- Explicit local first-derivative energy bound for the actual weak
principal equation. -/
theorem gradient_integral_le_explicit
    {Ω V W : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (hV : IsOpen V) (hVΩ : V ⊆ Ω) (hW : IsOpen W) (hWV : W ⊆ V)
    {η : E → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηV : tsupport η ⊆ V) (hηrange : range η ⊆ Icc (0 : ℝ) 1)
    (hηone : ∀ x ∈ W, η x = 1)
    {A N : ℝ} (hA : 0 ≤ A) (hN : 0 ≤ N)
    (ha : ∀ x ∈ tsupport η, ∀ i j : Fin d, |B.a x i j| ≤ A)
    (hDη : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N) :
    ∀ {u f : E → ℝ}, ContDiff ℝ ∞ u →
      MemLp u 2 (volume.restrict V) → MemLp f 2 (volume.restrict V) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
        (∫ x in V, B.principalIntegrand u φ x) = ∫ x in V, f x * φ x) →
      (∫ x in W, ∑ i : Fin d, (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2) ≤
        ((1 + (d : ℝ) ^ 2 * A * N ^ 2) / B.lam) *
          ((∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2) := by
  let Q : ℝ := (d : ℝ) ^ 2 * A * N ^ 2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hQbound (x : E) : |B.principalIntegrand η η x| ≤ Q :=
    abs_principal_cutoff_le_of_entry_bound B hA hN ha hDη x
  intro u f hu hum hfm heq
  let v : E → ℝ := fun x => η x * u x
  let φ : E → ℝ := fun x => (η x * η x) * u x
  have hv : ContDiff ℝ ∞ v := hη.mul hu
  have hφ : ContDiff ℝ ∞ φ := (hη.mul hη).mul hu
  have hvc : HasCompactSupport v := hηc.mul_right
  have hφc : HasCompactSupport φ := hηc.mul_right.mul_right
  have hφV : tsupport φ ⊆ V :=
    (tsupport_mul_subset_left.trans tsupport_mul_subset_left).trans hηV
  have henergy : Integrable (B.principalIntegrand v v) volume :=
    (B.continuous_principalIntegrand (hv.of_le (by simp)) (hv.of_le (by simp))).integrable_of_hasCompactSupport
      (principal_hasCompactSupport_right B v hvc)
  have htest : Integrable (B.principalIntegrand u φ) volume :=
    (B.continuous_principalIntegrand (hu.of_le (by simp)) (hφ.of_le (by simp))).integrable_of_hasCompactSupport
      (principal_hasCompactSupport_right B u hφc)
  have hcut : Integrable (fun x => u x ^ 2 * B.principalIntegrand η η x) volume :=
    ((hu.continuous.pow 2).mul
      (B.continuous_principalIntegrand (hη.of_le (by simp)) (hη.of_le (by simp)))).integrable_of_hasCompactSupport
        (principal_hasCompactSupport_right B η hηc).mul_left
  have hfφ : Integrable (fun x => f x * φ x) (volume.restrict V) :=
    hfm.integrable_mul ((hφ.continuous.memLp_of_hasCompactSupport
      (p := 2) hφc).restrict V)
  have hupper : (∫ x in V, B.principalIntegrand v v x) ≤
      (1 + Q) * ((∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2) := by
    have hid := heq φ hφ hφc hφV
    have hident : (∫ x in V, B.principalIntegrand v v x) =
        (∫ x in V, f x * φ x) + ∫ x in V, u x ^ 2 * B.principalIntegrand η η x := by
      simp_rw [show ∀ x, B.principalIntegrand v v x =
          B.principalIntegrand u φ x + u x ^ 2 * B.principalIntegrand η η x from
        principal_cutoff_identity B hη hu]
      rw [integral_add htest.restrict hcut.restrict, hid]
    rw [hident, ← integral_add hfφ hcut.restrict,
      ← integral_add hum.integrable_sq hfm.integrable_sq, ← integral_const_mul]
    apply integral_mono (hfφ.add hcut.restrict)
      ((hum.integrable_sq.add hfm.integrable_sq).const_mul (1 + Q))
    intro x
    have hηx := hηrange (mem_range_self x)
    have hηsq : (η x) ^ 2 ≤ 1 := by nlinarith [hηx.1, hηx.2]
    have habs : |f x * φ x| ≤ |f x * u x| := by
      dsimp only [φ]
      rw [show f x * (η x * η x * u x) = (η x)^2 * (f x * u x) by ring,
        abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_of_le_one_left (abs_nonneg _) hηsq
    have hfu : |f x * u x| ≤ (f x)^2 + (u x)^2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|f x| - |u x|), sq_abs (f x), sq_abs (u x)]
    have hcutbound : u x ^ 2 * B.principalIntegrand η η x ≤ u x ^ 2 * Q :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hQbound x)) (sq_nonneg _)
    have hsource := (le_abs_self (f x * φ x)).trans (habs.trans hfu)
    dsimp only [Pi.add_apply]
    nlinarith [mul_nonneg hQ (sq_nonneg (f x))]
  have hlow := gradient_integral_le_cutoff_principal_integral B hV hVΩ hW hWV
    hη hηc hηone hu
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ B.hlam_pos).mpr
  simpa only [mul_comm B.lam] using hlow.trans hupper

/-- Fixed nested sets and common numerical coefficient/ellipticity bounds
give one C before B, u and f. This is genuinely uniform across the family. -/
theorem exists_uniform_gradient_integral_le_on_nested_sets
    {Ω V W : Set E} (hV : IsOpen V) (hVΩ : V ⊆ Ω) (hW : IsOpen W)
    (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V)
    {κ A : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : SmoothEllipticBilinearForm d Ω), κ ≤ B.lam →
      (∀ x ∈ V, ∀ i j : Fin d, |B.a x i j| ≤ A) →
      ∀ {u f : E → ℝ}, ContDiff ℝ ∞ u →
        MemLp u 2 (volume.restrict V) → MemLp f 2 (volume.restrict V) →
        (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
          (∫ x in V, B.principalIntegrand u φ x) = ∫ x in V, f x * φ x) →
        (∫ x in W, ∑ i : Fin d, (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2) ≤
          C * ((∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2) := by
  obtain ⟨η, hη, hηc, hηrange, hηone, hηV, N, hN, hDη⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff_with_fderiv_bound hWc hV hWV
  let Q : ℝ := 1 + (d : ℝ) ^ 2 * A * N ^ 2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨Q / κ, div_nonneg hQ hκ.le, ?_⟩
  intro B hB ha u f hu hum hfm heq
  have h := gradient_integral_le_explicit B hV hVΩ hW (subset_closure.trans hWV)
    hη hηc hηV hηrange (fun x hx => hηone x (subset_closure hx))
    hA hN (fun x hx => ha x (hηV hx)) hDη hu hum hfm heq
  apply h.trans
  apply mul_le_mul_of_nonneg_right
  · exact div_le_div_of_nonneg_left hQ hκ hB
  · exact add_nonneg (integral_nonneg (fun x => sq_nonneg (u x)))
      (integral_nonneg (fun x => sq_nonneg (f x)))

#print axioms abs_principal_cutoff_le_of_entry_bound
#print axioms gradient_integral_le_explicit
#print axioms exists_uniform_gradient_integral_le_on_nested_sets

end Yamabe3.Analysis.UniformElliptic
