/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Sobolev/Boundary/LocalTangentialRegularity.lean

Retains the tangential weak-derivative construction and exposes its Riesz norm bound and
quantitative constant.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.BoundaryQuantitativeEstimate
import PoincareLib.Analysis.Sobolev.Euclidean.L2
/-! The actual tangential weak derivatives have a bound fixed before the
source and solution. Adapted from fixed LocalTangentialRegularity, retaining
the Riesz norm bound and the quantitative constant instead of discarding them.
This does not yet give a full H4 norm bound or sphere collar extension. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.BoundaryTangential
open Weak NirenbergEuclidean NirenbergCrossBoundsNonSmooth
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
private theorem diffQuot_indicator_eq_of_mem (v : E → ℝ)
    (k : Fin d) (hk : k ≠ 0) (h : ℝ) {x : E} (hx : x ∈ halfSpace d) :
    diffQuot k h ((halfSpace d).indicator v) x = diffQuot k h v x := by
  by_cases hh : h = 0
  · simp [hh]
  have hs : x + h • EuclideanSpace.single k 1 ∈ halfSpace d := by
    simpa [halfSpace, PiLp.add_apply, PiLp.smul_apply, hk.symm] using hx
  simp [diffQuot_apply_of_ne k hh, hx, hs]


/-- Geometry and coefficients fix U and all constants before choosing any
weak solution or source. Actual weak derivatives, not only difference
quotients, retain the bound. -/
theorem exists_uniform_flat_tangential_H2_bound
    (B : SmoothEllipticBilinearForm d univ)
    {W V : Set E} (hW : IsOpen W) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W) :
    ∃ (U : Set E) (C : Fin d → ℝ), IsOpen U ∧ IsCompact (closure U) ∧
      closure V ⊆ U ∧ U ⊆ W ∧ (∀ k, 0 ≤ C k) ∧
      ∀ (u f : E → ℝ) (p : Fin d → E → ℝ),
      MemW01p 2 u (halfSpace d) →
      MemLp f 2 (volume.restrict (W ∩ halfSpace d)) →
      (∀ i, MemLp (p i) 2 (volume.restrict (halfSpace d))) →
      (∀ i, HasWeakPartialDeriv i (p i) u (halfSpace d)) →
      (∀ j, MemLp (fun x => ∑ i : Fin d, B.a x i j * p i x)
        2 (volume.restrict (W ∩ halfSpace d))) →
      (∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ W ∩ halfSpace d →
        (∫ x in W ∩ halfSpace d, ∑ j : Fin d,
          (∑ i : Fin d, B.a x i j * p i x) *
            fderiv ℝ φ x (EuclideanSpace.single j 1)) =
          ∫ x in W ∩ halfSpace d, f x * φ x) →
      ∀ k : Fin d, k ≠ 0 → ∀ i : Fin d, ∃ q : E → ℝ,
        MemLp q 2 (volume.restrict (V ∩ halfSpace d)) ∧
        HasWeakPartialDeriv k q (p i) (V ∩ halfSpace d) ∧
        eLpNorm q 2 (volume.restrict (V ∩ halfSpace d)) ≤
          ENNReal.ofReal (Real.sqrt (C k *
            ((∫ x in U ∩ halfSpace d, ∑ j : Fin d, p j x ^ 2) +
             (∫ x in U ∩ halfSpace d, u x ^ 2) +
             (∫ x in U ∩ halfSpace d, f x ^ 2)))) := by
  classical
  obtain ⟨U₀, hU₀, hVU₀, hU₀c⟩ := exists_isOpen_superset_and_isCompact_closure hVc
  obtain ⟨U, hU, hVU, hUW₀⟩ := hVc.exists_isOpen_closure_subset
    ((hW.inter hU₀).mem_nhdsSet.mpr (subset_inter hVW hVU₀))
  have hUU₀ : closure U ⊆ U₀ := fun x hx => (hUW₀ hx).2
  have hUc : IsCompact (closure U) :=
    hU₀c.of_isClosed_subset isClosed_closure (hUU₀.trans subset_closure)
  have hUW : U ⊆ W := fun x hx => (hUW₀ (subset_closure hx)).1
  obtain ⟨η, hη, hηc, hηrange, hηone, hηU, N, hN, hDη⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff_with_fderiv_bound hVc hU hVU
  obtain ⟨R, hR, hRU⟩ := hηc.isCompact.exists_cthickening_subset_open hU hηU
  have hVH : IsOpen (V ∩ halfSpace d) := hV.inter isOpen_halfSpace
  have hVHc : IsCompact (closure (V ∩ halfSpace d)) :=
    hVc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  let C : Fin d → ℝ := fun k => nirenbergMasterYoungConstant B N hUc k / (B.lam / 2)
  refine ⟨U, C, hU, hUc, hVU, hUW, ?_, ?_⟩
  · intro k
    exact div_nonneg (nirenbergMasterYoungConstant_nonneg B hN hUc k)
      (div_pos B.hlam_pos (by norm_num)).le
  intro u f p hu hf hp hw hF heq
  let p₀ : Fin d → E → ℝ := fun i => (halfSpace d).indicator (p i)
  have hp₀ (i : Fin d) : MemLp (p₀ i) 2 volume :=
    (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr (hp i)
  intro k hk i
  have hC (h : ℝ) := flat_tangential_diffQuot_quantitative B hW hu hf hp hw hF heq
    hη hηc hηrange hN hDη hU (subset_univ _) hUc hUW hR
    (fun {h} hh => (Metric.cthickening_mono hh _).trans hRU)
    (fun x hx => hηone x (subset_closure hx)) hV.measurableSet k hk (h := h)
  let C₀ : ℝ := (nirenbergMasterYoungConstant B N hUc k * ((∫ x in U ∩ halfSpace d, ∑ j : Fin d, p j x ^ 2) +
    (∫ x in U ∩ halfSpace d, u x ^ 2) +
    (∫ x in U ∩ halfSpace d, f x ^ 2))) / (B.lam / 2)
  have hbound (h : ℝ) (hh : 0 < |h|) (hle : |h| ≤ R) :
      eLpNorm (diffQuot k h (p₀ i)) 2 (volume.restrict (V ∩ halfSpace d)) ≤
        ENNReal.ofReal (Real.sqrt C₀) := by
    have hq (j : Fin d) := (memLp_diffQuot_two k h (hp₀ j)).restrict (V ∩ halfSpace d)
    have hsq (j : Fin d) : Integrable (fun x => diffQuot k h (p₀ j) x ^ 2)
        (volume.restrict (V ∩ halfSpace d)) := (hq j).integrable_sq
    apply eLpNorm_two_le_sqrt_of_integral_sq_le (hq i)
    calc
      _ ≤ ∫ x in V ∩ halfSpace d, ∑ j : Fin d, diffQuot k h (p₀ j) x ^ 2 := by
        apply integral_mono (hsq i) (integrable_finsetSum _ (fun j _ => hsq j))
        intro x
        exact Finset.single_le_sum (fun j _ => sq_nonneg (diffQuot k h (p₀ j) x))
          (Finset.mem_univ i)
      _ = ∫ x in V ∩ halfSpace d, ∑ j : Fin d, diffQuot k h (p j) x ^ 2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hVH.measurableSet] with x hx
        apply Finset.sum_congr rfl
        intro j _
        rw [show diffQuot k h (p₀ j) x = diffQuot k h (p j) x from
          diffQuot_indicator_eq_of_mem (p j) k hk h hx.2]
      _ ≤ C₀ := (le_div_iff₀ (div_pos B.hlam_pos (by norm_num))).mpr (by
        simpa only [mul_comm] using hC h (abs_pos.mp hh) hle)
  obtain ⟨q, hq, hweak, hnorm⟩ := hasWeakPartialDeriv_of_diffQuot_uniform_bound_loc
    isOpen_univ hVH hVHc hR (subset_univ _) (by simpa using hp₀ i)
    k (Real.sqrt_nonneg C₀) hbound
  have hnorm' : eLpNorm q 2 (volume.restrict (V ∩ halfSpace d)) ≤
      ENNReal.ofReal (Real.sqrt (C k *
        ((∫ x in U ∩ halfSpace d, ∑ j : Fin d, p j x ^ 2) +
         (∫ x in U ∩ halfSpace d, u x ^ 2) +
         (∫ x in U ∩ halfSpace d, f x ^ 2)))) := by
    convert hnorm using 1 <;> dsimp [C₀, C] <;> congr 2 <;> ring
  refine ⟨q, hq, ?_, hnorm'⟩
  intro φ hφ hφc hφs
  calc
    _ = ∫ x in V ∩ halfSpace d, p₀ i x * fderiv ℝ φ x (EuclideanSpace.single k 1) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hVH.measurableSet] with x hx
      simp [p₀, hx.2]
    _ = _ := hweak φ hφ hφc hφs

#print axioms exists_uniform_flat_tangential_H2_bound
end Yamabe3.Analysis.UniformElliptic
