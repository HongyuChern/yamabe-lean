/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Sobolev/Boundary/H3.lean

Retains the symmetry-based transposition of the localized weak equation and adds a
uniform flat-boundary H2 estimate.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.BoundaryFullHessianBound
import Yamabe3.Analysis.BoundaryUniformTangential
import Yamabe3.Analysis.BoundaryLocalH4

/-! Quantitative full H2 regularity from the true zero-boundary H1 solution
and the original local weak equation. The intermediate H2 and tangential
bounds are proved, not imposed on the main statement. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.BoundaryTangential
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- This is only a named explicit bound, not a regularity predicate. -/
def flatTangentialBudget (U : Set E) (C : Fin d → ℝ)
    (u f : E → ℝ) (p : Fin d → E → ℝ) : ℝ≥0∞ :=
  ∑ k : Fin d, ENNReal.ofReal (Real.sqrt (C k *
    ((∫ x in U ∩ halfSpace d, ∑ j : Fin d, p j x ^ 2) +
      (∫ x in U ∩ halfSpace d, u x ^ 2) + (∫ x in U ∩ halfSpace d, f x ^ 2))))

/-- Geometry fixes all constants before source and solution. True zero
boundary H1 plus the actual equation produce H2 and control every actual
second weak derivative by lower-order solution energy and source L2. -/
theorem exists_uniform_flat_H2_bound
    (B : SmoothEllipticBilinearForm d univ)
    {W V : Set E} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W) :
    ∃ (U : Set E) (C : Fin d → ℝ) (A D : ℝ),
      IsOpen U ∧ IsCompact (closure U) ∧ closure V ⊆ U ∧ U ⊆ W ∧
      (∀ k, 0 ≤ C k) ∧ 0 ≤ A ∧ 0 ≤ D ∧
      ∀ (u f : E → ℝ) (p : Fin d → E → ℝ),
      MemW01p 2 u (halfSpace d) →
      MemLp f 2 (volume.restrict (W ∩ halfSpace d)) →
      (∀ i, MemLp (p i) 2 (volume.restrict (halfSpace d))) →
      (∀ i, HasWeakPartialDeriv i (p i) u (halfSpace d)) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ W ∩ halfSpace d →
        (∫ x in W ∩ halfSpace d, ∑ i, ∑ j, B.a x i j * p j x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          ∫ x in W ∩ halfSpace d, f x * φ x) →
      MemWkp 2 2 u (V ∩ halfSpace d) ∧
      ∀ i j : Fin d,
        eLpNorm (chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u (V ∩ halfSpace d))
          (V ∩ halfSpace d)) 2 (volume.restrict (V ∩ halfSpace d)) ≤
        flatTangentialBudget U C u f p + ENNReal.ofReal B.lam⁻¹ *
          (eLpNorm f 2 (volume.restrict (V ∩ halfSpace d)) + ENNReal.ofReal A *
            ((d : ℝ≥0∞) * d * flatTangentialBudget U C u f p) +
            ENNReal.ofReal D * ∑ ij : Fin d × Fin d,
              eLpNorm (p ij.2) 2 (volume.restrict (V ∩ halfSpace d))) := by
  classical
  have hVH := hV.inter isOpen_halfSpace
  have hWH := hW.inter isOpen_halfSpace
  have hVHc : IsCompact (closure (V ∩ halfSpace d)) :=
    hVc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  have hsub : V ∩ halfSpace d ⊆ W ∩ halfSpace d :=
    inter_subset_inter_left _ (subset_closure.trans hVW)
  obtain ⟨U, C, hU, hUc, hVU, hUW, hC, ht⟩ :=
    exists_uniform_flat_tangential_H2_bound B hW hV hVc hVW
  obtain ⟨A, D, hA, hD, hn⟩ := exists_uniform_hessian_bound_from_tangential B hVH hVHc
  refine ⟨U, C, A, D, hU, hUc, hVU, hUW, hC, hA, hD, ?_⟩
  intro u f p hu hf hp hw heq
  have hu2 := flat_local_H2_of_weakEquation B hW hWc hV hVc hVW hu hf hp hw heq
  have hpae (i : Fin d) : p i =ᵐ[volume.restrict (V ∩ halfSpace d)]
      chosenWeakPartial' 2 i u (V ∩ halfSpace d) :=
    HasWeakPartialDeriv.ae_eq hVH ((hw i).restrict hVH inter_subset_right)
      (chosenWeakPartial'_isWeakPartial_of_mem hu2.memW1p i)
      (((hp i).mono_measure (Measure.restrict_mono_set volume inter_subset_right)).locallyIntegrable
        (by norm_num))
      ((chosenWeakPartial'_memLp_of_mem hu2.memW1p i).locallyIntegrable (by norm_num))
  have heqV : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ V ∩ halfSpace d →
      (∫ x in V ∩ halfSpace d, ∑ i, ∑ j, B.a x i j *
        chosenWeakPartial' 2 j u (V ∩ halfSpace d) x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in V ∩ halfSpace d, f x * φ x := by
    intro φ hφ hc hs
    have hr := Poincare.Analysis.Elliptic.weakEquation_congr_restrict hsub
      (a := B.a) (q := p) (fun _ _ => rfl) (fun _ _ _ => rfl) heq φ hφ hc hs
    simp only [Finset.sum_mul] at hr
    rw [← hr]
    apply integral_congr_ae
    filter_upwards [eventually_all.mpr hpae] with x hx
    simp only [← hx]
  have hF (j : Fin d) : MemLp (fun x => ∑ i : Fin d, B.a x i j * p i x)
      2 (volume.restrict (W ∩ halfSpace d)) := by
    apply memLp_finsetSum
    intro i _
    obtain ⟨c, hc⟩ := hWc.exists_bound_of_continuousOn (B.continuous_a i j).continuousOn
    have hpW := (hp i).mono_measure (Measure.restrict_mono_set volume (show W ∩ halfSpace d ⊆ halfSpace d from inter_subset_right))
    apply hpW.of_le_mul (c := c) ((B.continuous_a i j).aestronglyMeasurable.mul hpW.1)
    filter_upwards [ae_restrict_mem hWH.measurableSet] with x hx
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (hc x (subset_closure hx.1)) (norm_nonneg _)
  have heqT : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ W ∩ halfSpace d →
      (∫ x in W ∩ halfSpace d, ∑ j : Fin d, (∑ i : Fin d, B.a x i j * p i x) *
        fderiv ℝ φ x (EuclideanSpace.single j 1)) = ∫ x in W ∩ halfSpace d, f x * φ x := by
    intro φ hφ hc hs
    rw [← heq φ hφ hc hs]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [B.symm x j i]
  have ht' (k : Fin d) (hk : k ≠ 0) (i : Fin d) :
      eLpNorm (chosenWeakPartial' 2 k (chosenWeakPartial' 2 i u (V ∩ halfSpace d))
        (V ∩ halfSpace d)) 2 (volume.restrict (V ∩ halfSpace d)) ≤ flatTangentialBudget U C u f p := by
    obtain ⟨q, hq, hwq, hqn⟩ := ht u f p hu hf hp hw hF heqT k hk i
    have hqp := hasWeakPartialDeriv_congr_ae hVH k (hpae i) hwq
    have hqchosen := chosenWeakPartial'_isWeakPartial_of_mem (hu2.chosenWeakPartial_mem i).memW1p k
    have hqae := HasWeakPartialDeriv.ae_eq hVH hqp hqchosen
      (hq.locallyIntegrable (by norm_num))
      ((chosenWeakPartial'_memLp_of_mem (hu2.chosenWeakPartial_mem i).memW1p k).locallyIntegrable (by norm_num))
    rw [← eLpNorm_congr_ae hqae]
    apply hqn.trans
    unfold flatTangentialBudget
    exact Finset.single_le_sum
      (f := fun k : Fin d => ENNReal.ofReal (Real.sqrt (C k *
        ((∫ x in U ∩ halfSpace d, ∑ j : Fin d, p j x ^ 2) +
         (∫ x in U ∩ halfSpace d, u x ^ 2) + (∫ x in U ∩ halfSpace d, f x ^ 2)))))
      (fun _ _ => zero_le) (Finset.mem_univ k)
  refine ⟨hu2, ?_⟩
  intro i j
  have h := hn u f hu2 (hf.mono_measure (Measure.restrict_mono_set volume hsub)) heqV
    (flatTangentialBudget U C u f p) ht' i j
  simpa only [← eLpNorm_congr_ae (hpae _)] using h

#print axioms exists_uniform_flat_H2_bound
end Yamabe3.Analysis.UniformElliptic
