/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Sobolev/Boundary/DifferentiatedEquation.lean

Uses the weak Hessian commutation argument with the explicitly recovered source on a
directional piece.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.DirectionalCommutatorRegularity
import Yamabe3.Analysis.SobolevLocalCompactExtension
import Yamabe3.Analysis.BoundaryQuantitativeInterfaces
import PoincareLib.Analysis.Sobolev.Boundary.NormalH3

/-! A source may be H1 only on one side of an interface. Actual global
tangential derivative witnesses still recover H3 up to that side. The
arbitrary open piece W need not have closure inside its own side. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryTangential Poincare.Analysis.Sobolev.BoundaryNormal
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem smoothElliptic_matrix_posDef (B : SmoothEllipticBilinearForm d univ) (x : E) :
    (B.a x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    exact B.symm x j i
  · intro v hv
    have hv' : (WithLp.toLp 2 v : E)≠0 := fun h => hv (congrArg WithLp.ofLp h)
    have hh := lt_of_lt_of_le (mul_pos B.hlam_pos (sq_pos_of_pos (norm_pos_iff.mpr hv')))
      (B.coercive x (mem_univ x) (WithLp.toLp 2 v))
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,matMulE_ofLp,
      PiLp.toLp_apply,WithLp.ofLp_toLp,Pi.star_apply,star_trivial,dotProduct_comm] using hh

theorem directional_source_H3_on_piece
    (B : SmoothEllipticBilinearForm d univ)
    {O V W : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V⊆O)
    (hW : IsOpen W) (hWV : W⊆V)
    {u f : E → ℝ} (hu : MemWkp 2 2 u O) (hf : MemLp f 2 (volume.restrict O))
    (hfW : MemW1p 2 f W) (hr : ∀k : Fin d,k≠0 → DirectionalL2 k f O)
    (heq : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆O →
      (∫ x in O,∑ i,∑ j,B.a x i j*chosenWeakPartial' 2 j u O x*
        fderiv ℝ φ x (EuclideanSpace.single i 1))=∫ x in O,f x*φ x) :
    MemWkp 3 2 u W := by
  have hWc : IsCompact (closure W) := hVc.of_isClosed_subset isClosed_closure (closure_mono hWV)
  have hWO : W⊆O := hWV.trans (subset_closure.trans hVO)
  have huW := hu.mono_set (by norm_num : (1:ℝ≥0∞)≤2) hW hWO
  have htan (k : Fin d) (hk : k≠0) : MemWkp 2 2 (chosenWeakPartial' 2 k u W) W := by
    obtain ⟨_,r,hr,hfr⟩ := hr k hk
    have hlocal := directional_weak_source_local_H2 hO hOc B.a B.smooth_a
      (fun x _ => smoothElliptic_matrix_posDef B x) hu hf hr k hfr heq
    have hpV := memWkp_on_precompact_of_locally hlocal hV hVc hVO
    have hpW := hpV.mono_set (by norm_num : (1:ℝ≥0∞)≤2) hW hWV
    exact (MemWkp_congr_ae (by norm_num) hW
      (chosenWeakPartial'_mono_set_ae (by norm_num) hW hWO hu.memW1p k)).mp hpW
  exact memWkp_three_of_tangential_memWkp_two B hW hWc huW hfW htan
    (localized_principal_restrict_canonical hW hWO hu.memW1p heq)

theorem explicit_directional_source_equation
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (A : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i j,ContDiff ℝ ∞ (fun x => A x i j))
    {u f r : E → ℝ} (hu : MemWkp 2 2 u O)
    (hf : MemLp f 2 (volume.restrict O)) (hr : MemLp r 2 (volume.restrict O))
    (k : Fin d) (hfr : HasWeakPartialDeriv k r f O)
    (heq : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆O →
      (∫ x in O,∑ i,∑ j,A x i j*chosenWeakPartial' 2 j u O x*
        fderiv ℝ φ x (EuclideanSpace.single i 1))=∫ x in O,f x*φ x) :
    let G := differentiatedSource A (fun j => chosenWeakPartial' 2 j u O)
      (fun i j => chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u O) O) r k
    MemLp G 2 (volume.restrict O) ∧
      ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆O →
        (∫ x in O,∑ i,∑ j,A x i j*
          chosenWeakPartial' 2 j (chosenWeakPartial' 2 k u O) O x*
          fderiv ℝ φ x (EuclideanSpace.single i 1))=∫ x in O,G x*φ x := by
  let p (j : Fin d) := chosenWeakPartial' 2 j u O
  let q (i j : Fin d) := chosenWeakPartial' 2 j (p i) O
  have hp (j : Fin d) : MemW1p 2 (p j) O := (hu.chosenWeakPartial_mem j).memW1p
  have hq (i j : Fin d) : MemLp (q i j) 2 (volume.restrict O) :=
    chosenWeakPartial'_memLp_of_mem (hp i) j
  have hw (i j : Fin d) : HasWeakPartialDeriv i (q i j) (p j) O :=
    weakPartial_commute i j
      (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i)
      (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p j)
      (chosenWeakPartial'_isWeakPartial_of_mem (hp i) j)
  have he := differentiated_weak_divergence hO hOc A hA k (fun j => (hp j).1) hq hw hf hr hfr heq
  have hfun : (fun x => r x+∑i,∑j,
      (fderiv ℝ (fun y => fderiv ℝ (fun z => A z i j) y (EuclideanSpace.single k 1)) x
        (EuclideanSpace.single i 1)*p j x+
        fderiv ℝ (fun y => A y i j) x (EuclideanSpace.single k 1)*q i j x))=
      differentiatedSource A p q r k := by
    funext x
    simp only [differentiatedSource,partialDeriv]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    unfold partialDeriv
    ring
  rw [hfun] at he
  exact he

#print axioms smoothElliptic_matrix_posDef
#print axioms directional_source_H3_on_piece
#print axioms explicit_directional_source_equation
end Yamabe3.Analysis.UniformElliptic
