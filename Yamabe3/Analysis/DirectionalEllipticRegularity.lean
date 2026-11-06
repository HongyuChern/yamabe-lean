/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Sobolev/Boundary/DifferentiatedEquation.lean

Uses the weak Hessian commutation argument to construct the source for a directional
differentiated equation.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.BoundaryWeakSourceBootstrap
import PoincareLib.Analysis.Elliptic.Regularity.Iteration.Bootstrap

/-! A single actual L2 weak derivative of the source suffices to gain
local H2 for the same directional derivative of an H2 solution. Full H1
of a discontinuous transmission source is not assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryTangential
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_directional_weak_source
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (A : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i j,ContDiff ℝ ∞ (fun x => A x i j))
    {u f r : E → ℝ} (hu : MemWkp 2 2 u O)
    (hf : MemLp f 2 (volume.restrict O)) (hr : MemLp r 2 (volume.restrict O))
    (k : Fin d) (hfr : HasWeakPartialDeriv k r f O)
    (heq : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆O →
      (∫ x in O,∑ i,∑ j,A x i j*chosenWeakPartial' 2 j u O x*
        fderiv ℝ φ x (EuclideanSpace.single i 1))=∫ x in O,f x*φ x) :
    ∃ G : E → ℝ,MemLp G 2 (volume.restrict O) ∧
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
  exact ⟨_,differentiated_weak_divergence hO hOc A hA k
    (fun j => (hp j).1) hq hw hf hr hfr heq⟩

theorem directional_weak_source_local_H2
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (A : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i j,ContDiff ℝ ∞ (fun x => A x i j))
    (hpos : ∀ x∈O,(A x).PosDef)
    {u f r : E → ℝ} (hu : MemWkp 2 2 u O)
    (hf : MemLp f 2 (volume.restrict O)) (hr : MemLp r 2 (volume.restrict O))
    (k : Fin d) (hfr : HasWeakPartialDeriv k r f O)
    (heq : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆O →
      (∫ x in O,∑ i,∑ j,A x i j*chosenWeakPartial' 2 j u O x*
        fderiv ℝ φ x (EuclideanSpace.single i 1))=∫ x in O,f x*φ x) :
    MemWkpLocally 2 (chosenWeakPartial' 2 k u O) O := by
  obtain ⟨G,hG,hGeq⟩ := exists_directional_weak_source hO hOc A hA hu hf hr k hfr heq
  have hk := hu.chosenWeakPartial_mem k
  intro x hx
  apply exists_memWkp_two_of_weakEquation hO A _ G
    (fun i => chosenWeakPartial' 2 i (chosenWeakPartial' 2 k u O) O)
    (fun i j => (hA i j).contDiffOn) hpos
    (fun K _ hKO => hk.memLp.mono_measure (Measure.restrict_mono hKO le_rfl))
    (fun i K _ hKO => (chosenWeakPartial'_memLp_of_mem hk.memW1p i).mono_measure
      (Measure.restrict_mono hKO le_rfl))
    (fun K _ hKO => hG.mono_measure (Measure.restrict_mono hKO le_rfl))
    (fun i => chosenWeakPartial'_isWeakPartial_of_mem hk.memW1p i) hGeq hx

#print axioms exists_directional_weak_source
#print axioms directional_weak_source_local_H2
end Yamabe3.Analysis.UniformElliptic
