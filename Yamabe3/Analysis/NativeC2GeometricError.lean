/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Elliptic/Regularity/InteriorEstimates/Operators/Basic.lean

Adapts the coordinate principal-source expansion to the second-order operator evaluated
at a point for C2 functions.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.FiniteRegularityWeakJets
import Yamabe3.Analysis.NativeWeakSmallGeometricError

/-! The actual classical native divergence error on C2 representatives
agrees with the weak error and inherits its small H4-to-H2 bound. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ENNReal Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem principalSource_eq_secondOrderOperator_C2_at
    {a : E → Matrix (Fin 3) (Fin 3) ℝ} (b : Fin 3 → E → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    {u : E → ℝ} (x : E) (hu : ContDiffAt ℝ 2 u x) :
    principalSource a u x = -secondOrderOperator a b u x +
      ∑ j, (b j x - ∑ i, partialDeriv i (fun y => a y i j) x) * partialDeriv j u x := by
  have hpartial (j : Fin 3) : ContDiffAt ℝ 1 (partialDeriv j u) x :=
    (hu.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have hd (i j) : DifferentiableAt ℝ (fun y => a y i j * partialDeriv j u y) x :=
    ((ha i j).contDiffAt.of_le (by norm_num) |>.mul (hpartial j)).differentiableAt (by norm_num)
  have hprod (i j) : partialDeriv i (fun y => a y i j * partialDeriv j u y) x =
      a x i j * partialDeriv i (partialDeriv j u) x +
        partialDeriv i (fun y => a y i j) x * partialDeriv j u x := by
    change (fderiv ℝ (fun y => a y i j * partialDeriv j u y) x)
      (EuclideanSpace.single i 1) = _
    rw [fderiv_fun_mul ((ha i j).differentiable (by simp) x)
      ((hpartial j).differentiableAt (by norm_num))]
    simp only [add_apply, smul_apply, smul_eq_mul, partialDeriv]
    ring
  have hflux (i) : partialDeriv i (matrixFlux a (fun j => partialDeriv j u) i) x =
      ∑ j, (a x i j * partialDeriv i (partialDeriv j u) x +
        partialDeriv i (fun y => a y i j) x * partialDeriv j u x) := by
    change (fderiv ℝ (fun y => ∑ j, a y i j * partialDeriv j u y) x)
      (EuclideanSpace.single i 1) = _
    rw [fderiv_fun_sum (fun j _ => hd i j)]
    simp only [sum_apply]
    exact Finset.sum_congr rfl (fun j _ => hprod i j)
  unfold principalSource secondOrderOperator
  simp_rw [hflux, Finset.sum_add_distrib, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul]
  rw [Finset.sum_comm (f := fun j i =>
    partialDeriv i (fun y => a y i j) x * partialDeriv j u x)]
  ring


theorem nativeScaledGeometricError_eq_negative_principalSource_C2_at
    (g : RiemannianMetric 3 E) (r : ℝ) {u : E → ℝ} (x : E)
    (hu : ContDiffAt ℝ 2 u x) :
    nativeScaledGeometricError g r u x =
      -principalSource (fun z => nativeDivergenceMatrix g (r • z) - 1) u x := by
  let a := fun z => nativeDivergenceMatrix g (r • z) - 1
  have ha : ∀ i j : Fin 3, ContDiff ℝ ∞ (fun z => a z i j) :=
    contDiff_nativeScaledPrincipalError g r
  change secondOrderPerturbation (fun i j z => a z i j)
    (fun j z => ∑ i : Fin 3, partialDeriv i (fun y => a y i j) z) (fun _ => 0) u x = -principalSource a u x
  rw [principalSource_eq_secondOrderOperator_C2_at (fun _ _ => 0) ha x hu]
  simp only [secondOrderPerturbation,secondOrderOperator,zero_mul,Finset.sum_const_zero,add_zero,
    zero_sub,neg_mul,Finset.sum_neg_distrib]
  ring

theorem nativeWeakScaledGeometricError_classical_ae
    (g : RiemannianMetric 3 E) (r : ℝ) {O W : Set E}
    (hO : IsOpen O) (hOc : IsCompact (closure O)) (hW : IsOpen W) (hOW : closure O ⊆ W)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u W) (hu2 : MemWkp 2 2 u O) :
    nativeWeakScaledGeometricError g r O u =ᵐ[volume.restrict O] nativeScaledGeometricError g r u :=
  weakSecondOrderPerturbation_classical_ae hO hOc hW hOW hu hu2 _ _ _

#print axioms principalSource_eq_secondOrderOperator_C2_at
#print axioms nativeScaledGeometricError_eq_negative_principalSource_C2_at
#print axioms nativeWeakScaledGeometricError_classical_ae
end Yamabe3.Analysis.UniformElliptic
