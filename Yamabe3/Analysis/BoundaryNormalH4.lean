/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Sobolev/Boundary/NormalH3.lean

Adapts the tangential-to-normal recovery interface from order three to order four.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.BoundaryWeakSourceBootstrap
import PoincareLib.Analysis.Sobolev.Boundary.NormalH3

/-!
# Fourth-order normal recovery from the actual elliptic equation

Tangential H3 of the first derivatives plus the original H2 source and
existing H3 solution recover the missing normal fourth derivatives.
This auxiliary conditional step does not assume or assert a half-end solver.
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
open Poincare.Analysis.Sobolev.BoundaryNormal
open Poincare.Analysis.Sobolev.NirenbergEuclidean
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem memWkp_four_of_tangential_memWkp_three
    (B : SmoothEllipticBilinearForm d univ)
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    {u f : E → ℝ} (hu : MemWkp 3 2 u O) (hf : MemWkp 2 2 f O)
    (htan : ∀ k : Fin d, k ≠ 0 → MemWkp 3 2 (chosenWeakPartial' 2 k u O) O)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u O x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x) :
    MemWkp 4 2 u O := by
  let p (i : Fin d) := chosenWeakPartial' 2 i u O
  have hp (i : Fin d) : MemWkp 2 2 (p i) O := hu.chosenWeakPartial_mem i
  have hw (i : Fin d) : HasWeakPartialDeriv i (p i) u O :=
    chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i
  obtain ⟨F, hF, hFeq⟩ := exists_differentiated_sobolev_source 1 hO hOc
    B.a B.smooth_a hu hf heq 0
  have hptan (k : Fin d) (hk : k ≠ 0) :
      MemWkp 2 2 (chosenWeakPartial' 2 k (p 0) O) O := by
    let v := chosenWeakPartial' 2 0 (p k) O
    have hv : MemWkp 2 2 v O := (htan k hk).chosenWeakPartial_mem 0
    have hwv : HasWeakPartialDeriv k v (p 0) O :=
      weakPartial_commute k 0 (hw k) (hw 0)
        (chosenWeakPartial'_isWeakPartial_of_mem (hp k).memW1p 0)
    have hq := chosenWeakPartial'_isWeakPartial_of_mem (hp 0).memW1p k
    have hae : v =ᵐ[volume.restrict O] chosenWeakPartial' 2 k (p 0) O :=
      HasWeakPartialDeriv.ae_eq hO hwv hq (hv.memLp.locallyIntegrable (by norm_num))
        ((chosenWeakPartial'_memLp_of_mem (hp 0).memW1p k).locallyIntegrable (by norm_num))
    exact (MemWkp_congr_ae (by norm_num) hO hae).mp hv
  have hp0 : MemWkp 3 2 (p 0) O :=
    memWkp_three_of_tangential_memWkp_two B hO hOc (hp 0) hF.memW1p hptan hFeq
  refine ⟨hu.memW1p, fun i => ?_⟩
  by_cases hi : i = 0
  · simpa only [hi] using hp0
  · exact htan i hi

#print axioms memWkp_four_of_tangential_memWkp_three
end Yamabe3.Analysis.UniformElliptic

