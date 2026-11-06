/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Sobolev/Boundary/DifferentiatedEquation.lean

Uses the compact-coefficient L2 multiplication estimate in the boundary weak Hessian
identity.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.BoundaryStrongEquation

/-! The same source and actual weak Hessian satisfy the nondivergence form
identity almost everywhere, including coefficient first derivatives. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem compact_coeff_mul {O : Set E} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) {a v : E → ℝ} (ha : Continuous a)
    (hv : MemLp v 2 (volume.restrict O)) :
    MemLp (fun x => a x * v x) 2 (volume.restrict O) := by
  obtain ⟨C, hC⟩ := hOc.exists_bound_of_continuousOn ha.continuousOn
  apply hv.of_le_mul (c := C) (ha.aestronglyMeasurable.mul hv.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x (subset_closure hx)) (norm_nonneg _)

/-- Actual weak Hessian identity: the source sign and coefficient derivative
terms follow from the original weak equation, without a classical solution. -/
theorem weak_hessian_equation_ae
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (a : E → Matrix (Fin d) (Fin d) ℝ) (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    {u f : E → ℝ} (hu : MemWkp 2 2 u O) (hf : MemLp f 2 (volume.restrict O))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, a x i j * chosenWeakPartial' 2 j u O x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x) :
    (fun x => ∑ i, ∑ j,
      (a x i j * chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u O) O x +
        fderiv ℝ (fun y => a y i j) x (EuclideanSpace.single i 1) *
          chosenWeakPartial' 2 j u O x)) =ᵐ[volume.restrict O] (fun x => -f x) := by
  let p (j : Fin d) := chosenWeakPartial' 2 j u O
  let q (i j : Fin d) := chosenWeakPartial' 2 i (p j) O
  let r (i j : Fin d) (x : E) := a x i j * q i j x +
    fderiv ℝ (fun y => a y i j) x (EuclideanSpace.single i 1) * p j x
  have hp (j : Fin d) := (hu.chosenWeakPartial_mem j).memW1p
  have hq (i j : Fin d) : MemLp (q i j) 2 (volume.restrict O) :=
    chosenWeakPartial'_memLp_of_mem (hp j) i
  have hval (i j : Fin d) : MemLp (fun x => a x i j * p j x) 2 (volume.restrict O) :=
    compact_coeff_mul hO hOc (ha i j).continuous (hp j).1
  have hr (i j : Fin d) : MemLp (r i j) 2 (volume.restrict O) :=
    (compact_coeff_mul hO hOc (ha i j).continuous (hq i j)).add
      (compact_coeff_mul hO hOc (((ha i j).continuous_fderiv (by simp)).clm_apply continuous_const)
        (hp j).1)
  have hwr (i j : Fin d) : HasWeakPartialDeriv i (r i j) (fun x => a x i j * p j x) O :=
    (chosenWeakPartial'_isWeakPartial_of_mem (hp j) i).mul_smooth hO (ha i j)
      ((hp j).1.locallyIntegrable (by norm_num)) ((hq i j).locallyIntegrable (by norm_num))
  apply divergence_eq_neg_source_ae hO
    (F := fun i x => ∑ j, a x i j * p j x) (D := fun i x => ∑ j, r i j x)
    (fun i => memLp_finsetSum _ (fun j _ => hval i j))
    (fun i => memLp_finsetSum _ (fun j _ => hr i j)) hf
  · intro i φ hφ hc hs
    have hφLp : MemLp φ 2 (volume.restrict O) :=
      (hφ.continuous.memLp_of_hasCompactSupport hc).restrict O
    have hDLp : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))
        2 (volume.restrict O) :=
      (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hc.fderiv_apply ℝ _)).restrict O
    have hs1 := integral_finsetSum Finset.univ (fun j _ => (hval i j).integrable_mul hDLp)
    have hs2 := integral_finsetSum Finset.univ (fun j _ => (hr i j).integrable_mul hφLp)
    simp only [Pi.mul_apply] at hs1 hs2
    simp_rw [Finset.sum_mul]
    rw [hs1, hs2, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => hwr i j φ hφ hc hs
  · intro φ hφ hc hs
    simpa only [p, Finset.sum_mul] using heq φ hφ hc hs

#print axioms weak_hessian_equation_ae
end Yamabe3.Analysis.UniformElliptic
