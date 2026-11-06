/-
Copyright (c) 2026 The PoincareLib contributors.
Copyright 2026 The DifferentialGeometry contributors
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Elliptic/Regularity/Representative.lean
Earlier source credited by PoincareLib at DifferentialGeometry 1b535dd102b94cc42b107cca27059687888f08b3.
  DifferentialGeometry/Analysis/Sobolev/Euclidean/Embedding/IteratedSobolevEmbedding.lean

Specializes the countable-cover and almost-everywhere gluing argument for smooth
representatives to C2 representatives.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.CompactWeakH4Representative
import Yamabe3.Analysis.SobolevLocalCompactExtension
import PoincareLib.Analysis.Elliptic.Regularity.Representative

/-! C2 gluing uses the proved countable-cover argument in the pinned
Poincare Representative module, specialized to order two. This project
adaptation keeps its overlap and volume-a.e. identification argument.
Then actual local weak H4 produces each local representative. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped ENNReal ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)
theorem exists_C2_representative_of_local {O : Set E} {u : E → ℝ}
    (hlocal : ∀ x ∈ O, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧
      ∃ f : E → ℝ, ContDiffOn ℝ 2 f V ∧ f =ᵐ[volume.restrict V] u) :
    ∃ U : E → ℝ, ContDiffOn ℝ 2 U O ∧ U =ᵐ[volume.restrict O] u := by
  classical
  choose V hV hxV hVO f hf hfu using fun x : O => hlocal x x.property
  have hcover : O ⊆ ⋃ x : O, V x := fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  have hagree : ∀ (x y : O) (z : E), z ∈ V x → z ∈ V y → f x z = f y z := by
    intro x y z hzx hzy
    exact eqOn_inter_of_ae_eq (hV x) (hV y) (hf x).continuousOn
      (hf y).continuousOn (hfu x) (hfu y) ⟨hzx, hzy⟩
  let g : O → ℝ := Set.iUnionLift V (fun x z => f x z)
    (fun x y z hzx hzy => hagree x y z hzx hzy) O hcover
  let U : E → ℝ := fun x => if hx : x ∈ O then g ⟨x, hx⟩ else 0
  have hU : ∀ x : O, EqOn U (f x) (V x) := by
    intro x z hz
    have hzO : z ∈ O := hVO x hz
    have hglue : g ⟨z, hzO⟩ = f x z := Set.iUnionLift_of_mem
      (S := V) (T := O) ⟨z, hzO⟩ hz
    simpa only [U, dif_pos hzO] using hglue
  refine ⟨U, ?_, ?_⟩
  · apply contDiffOn_of_locally_contDiffOn
    intro x hx
    refine ⟨V ⟨x, hx⟩, hV ⟨x, hx⟩, hxV ⟨x, hx⟩, ?_⟩
    exact ((hf ⟨x, hx⟩).mono inter_subset_right).congr
      (fun y hy => hU ⟨x, hx⟩ hy.2)
  · obtain ⟨T, hT, hTcover⟩ := TopologicalSpace.isOpen_iUnion_countable V hV
    have hOcover : O ⊆ ⋃ x ∈ T, V x := by rwa [hTcover]
    have hlocal_ae : ∀ x ∈ T, U =ᵐ[volume.restrict (V x)] u := by
      intro x _
      apply Filter.EventuallyEq.trans _ (hfu x)
      exact (ae_restrict_iff' (hV x).measurableSet).mpr
        (Filter.Eventually.of_forall fun z hz => hU x hz)
    exact ae_restrict_of_ae_restrict_of_subset hOcover
      ((ae_eq_restrict_biUnion_iff V hT U u).mpr hlocal_ae)

theorem exists_local_weak_H4_C2_representative {O : Set E} (hO : IsOpen O)
    {u : E → ℝ} (hu : MemWkpLocally 4 u O) :
    ∃ F : E → ℝ, ContDiffOn ℝ 2 F O ∧ F =ᵐ[volume.restrict O] u := by
  apply exists_C2_representative_of_local
  intro x hx
  obtain ⟨v,U,hU,hxU,hvc,hv,heq⟩ := exists_compact_sobolev_extension_near_compact hu
    (isCompact_singleton (x := x)) (singleton_subset_iff.mpr hx)
  obtain ⟨F,φ,hF,hFv,-⟩ := exists_compact_weak_H4_C2_representative hv hvc
  refine ⟨U ∩ O,hU.inter hO,⟨hxU (mem_singleton x),hx⟩,inter_subset_right,F,hF.contDiffOn,?_⟩
  filter_upwards [ae_restrict_of_ae hFv,ae_restrict_mem (hU.inter hO).measurableSet] with y hy hyU
  exact hy.trans (heq hyU.1)

#print axioms exists_C2_representative_of_local
#print axioms exists_local_weak_H4_C2_representative
end Yamabe3.Analysis.UniformElliptic
