/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Sobolev/Boundary/H3.lean
  PoincareLib/Analysis/Sobolev/Boundary/Regularity/Tangential.lean

Adapts the local principal H2 and tangential arguments for the cutoff localization step
in the boundary H4 proof.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.BoundaryFlatH4
import PoincareLib.Analysis.Sobolev.Boundary.H3
import PoincareLib.Analysis.Sobolev.Boundary.Localization.WeakEquation

/-! Local boundary H4 from the actual zero-boundary H1 weak solution.
The H2 proof is adapted from fixed Poincare Boundary/H3's private local-principal
proof, with no fixed source modifications. Membership only; no norm estimate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.BoundaryTangential
open Poincare.Analysis.Sobolev.BoundaryLocalization
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem principal_restrict {O V : Set E} (hs : V ⊆ O)
    {a : E → Matrix (Fin d) (Fin d) ℝ} {p : Fin d → E → ℝ} {f : E → ℝ}
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, a x i j * p j x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ x in V, ∑ i, ∑ j, a x i j * p j x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in V, f x * φ x := by
  intro φ hφ hc ht
  simpa only [Finset.sum_mul] using
    Poincare.Analysis.Elliptic.weakEquation_congr_restrict hs
      (a := a) (q := p) (fun _ _ => rfl) (fun _ _ _ => rfl) heq φ hφ hc ht

omit [NeZero d] in
private theorem memLp_coeff_mul {W O : Set E} (hWc : IsCompact (closure W))
    (hO : IsOpen O) (hs : O ⊆ W) {a v : E → ℝ} (ha : Continuous a)
    (hv : MemLp v 2 (volume.restrict O)) :
    MemLp (fun x => a x * v x) 2 (volume.restrict O) := by
  obtain ⟨C, hC⟩ := hWc.exists_bound_of_continuousOn ha.continuousOn
  apply hv.of_le_mul (c := C) (ha.aestronglyMeasurable.mul hv.1)
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x (subset_closure (hs hx))) (norm_nonneg _)

omit [NeZero d] in
private theorem memLp_compact_mul {O : Set E} {a v : E → ℝ}
    (ha : Continuous a) (hc : HasCompactSupport a)
    (hv : MemLp v 2 (volume.restrict O)) :
    MemLp (fun x => a x * v x) 2 (volume.restrict O) := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous ha
  apply hv.of_le_mul (c := C) (ha.aestronglyMeasurable.mul hv.1)
  exact Eventually.of_forall fun x => by
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

theorem flat_local_H2_of_weakEquation
    (B : SmoothEllipticBilinearForm d univ)
    {W V : Set E} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W)
    {u f : E → ℝ} {p : Fin d → E → ℝ}
    (hu : MemW01p 2 u (halfSpace d))
    (hf : MemLp f 2 (volume.restrict (W ∩ halfSpace d)))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict (halfSpace d)))
    (hw : ∀ i, HasWeakPartialDeriv i (p i) u (halfSpace d))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ W ∩ halfSpace d →
      (∫ x in W ∩ halfSpace d, ∑ i, ∑ j, B.a x i j * p j x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in W ∩ halfSpace d, f x * φ x) :
    MemWkp 2 2 u (V ∩ halfSpace d) := by
  have hWH := hW.inter isOpen_halfSpace
  have hVH := hV.inter isOpen_halfSpace
  have hsub : V ∩ halfSpace d ⊆ W ∩ halfSpace d :=
    inter_subset_inter_left _ (subset_closure.trans hVW)
  have hF (j : Fin d) : MemLp (fun x => ∑ i : Fin d, B.a x i j * p i x)
      2 (volume.restrict (W ∩ halfSpace d)) :=
    memLp_finsetSum _ (fun i _ => memLp_coeff_mul hWc hWH inter_subset_left
      (B.smooth_a i j).continuous
      ((hp i).mono_measure (Measure.restrict_mono_set volume inter_subset_right)))
  have heq' : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ W ∩ halfSpace d →
      (∫ x in W ∩ halfSpace d, ∑ j : Fin d,
        (∑ i : Fin d, B.a x i j * p i x) *
          fderiv ℝ φ x (EuclideanSpace.single j 1)) =
        ∫ x in W ∩ halfSpace d, f x * φ x := by
    intro φ hφ hc hs
    rw [← heq φ hφ hc hs]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [B.symm x j i]
  apply Poincare.Analysis.Sobolev.BoundaryNormal.memWkp_two_of_tangential_weakDerivatives B hVH
    (hVc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left))
    (hu.1.1.mono_measure (Measure.restrict_mono_set volume inter_subset_right))
    (hf.mono_measure (Measure.restrict_mono_set volume hsub))
    (fun i => (hp i).mono_measure (Measure.restrict_mono_set volume inter_subset_right))
    (fun i => (hw i).restrict hVH inter_subset_right)
    (exists_tangential_weakPartial_of_local_weakEquation B hW hV hVc hVW hu hf hp hw hF heq')
  exact principal_restrict hsub heq


private theorem canonical_local_equation
    {O W : Set E} (hW : IsOpen W) (hs : W ⊆ O)
    {a : E → Matrix (Fin d) (Fin d) ℝ} {u f : E → ℝ}
    (hu : MemW1p 2 u O)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, a x i j * chosenWeakPartial' 2 j u O x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W →
      (∫ x in W, ∑ i, ∑ j, a x i j * chosenWeakPartial' 2 j u W x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in W, f x * φ x := by
  intro φ hφ hc ht
  rw [← principal_restrict hs heq φ hφ hc ht]
  apply integral_congr_ae
  filter_upwards [eventually_all.mpr (fun j =>
    chosenWeakPartial'_mono_set_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2) hW hs hu j)] with x hx
  simp only [← hx]

/-- H4 on compact portions of the true flat zero Dirichlet boundary.
Only H1 zero boundary, local H2 source, and the original weak equation
are inputs: no H2/H3/H4 solution regularity is assumed. -/
theorem flat_local_H4_of_weakEquation
    (B : SmoothEllipticBilinearForm d univ)
    {W V : Set E} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W)
    {u f : E → ℝ} (hu0 : MemW01p 2 u (halfSpace d))
    (hf : MemWkp 2 2 f (W ∩ halfSpace d))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ W ∩ halfSpace d →
      (∫ x in W ∩ halfSpace d, ∑ i, ∑ j, B.a x i j *
        chosenWeakPartial' 2 j u (halfSpace d) x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in W ∩ halfSpace d, f x * φ x) :
    MemWkp 4 2 u (V ∩ halfSpace d) := by
  let H := halfSpace d
  obtain ⟨U, hU, hVU, hUW, hUc⟩ := exists_open_between_and_isCompact_closure hVc hW hVW
  obtain ⟨T, hT, hUT, hTW, hTc⟩ := exists_open_between_and_isCompact_closure hUc hW hUW
  have hUH := hU.inter (isOpen_halfSpace (d := d))
  have hTH := hT.inter (isOpen_halfSpace (d := d))
  have hVH := hV.inter (isOpen_halfSpace (d := d))
  have hTW' : T ∩ H ⊆ W ∩ H := inter_subset_inter_left _ (subset_closure.trans hTW)
  have hUT' : U ∩ H ⊆ T ∩ H := inter_subset_inter_left _ (subset_closure.trans hUT)
  have hu2 := flat_local_H2_of_weakEquation B hW hWc hT hTc hTW hu0
    hf.memW1p.1 (fun j => chosenWeakPartial'_memLp_of_mem hu0.1 j)
    (fun j => chosenWeakPartial'_isWeakPartial_of_mem hu0.1 j) heq
  have hcan : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ T ∩ H →
      (∫ x in T ∩ H, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u (T ∩ H) x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in T ∩ H, f x * φ x := by
    intro φ hφ hc hs
    rw [← principal_restrict hTW' heq φ hφ hc hs]
    apply integral_congr_ae
    filter_upwards [eventually_all.mpr (fun j =>
      chosenWeakPartial'_mono_set_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        hTH inter_subset_right hu0.1 j)] with x hx
    change (∑ i : Fin d, ∑ j : Fin d, B.a x i j *
      chosenWeakPartial' 2 j u (T ∩ H) x * fderiv ℝ φ x (EuclideanSpace.single i 1)) = _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← hx j]
  have hfT := hf.mono_set (by norm_num : (1 : ℝ≥0∞) ≤ 2) hTH hTW'
  obtain ⟨χ, hχ, hc, -, hone, hs⟩ := SmoothEllipticBilinearForm.exists_cutoff hUc hT hUT
  have hloc := localize_weak_divergence 1 isOpen_halfSpace hT B.a B.smooth_a
    hu2 hfT.le_succ hχ hc hs hcan
  have hv0 := memW01p_mul_smooth isOpen_halfSpace hu0 hχ hc
  have hv2 := memWkp_mul_smooth_of_tsupport_subset 2 isOpen_halfSpace hT hu2 hχ hc hs
  have hv3 := memWkp_three_of_weakEquation B hU hUc hv0 hv2 hloc.1.memW1p hloc.2
  have hu3 : MemWkp 3 2 u (U ∩ H) := by
    apply (MemWkp_congr_ae (by norm_num) hUH (u := fun x => χ x * u x) ?_).mp hv3
    filter_upwards [ae_restrict_mem hUH.measurableSet] with x hx
    rw [hone x (subset_closure hx.1), one_mul]
  obtain ⟨ψ, hψ, hψc, -, hψone, hψs⟩ := SmoothEllipticBilinearForm.exists_cutoff hVc hU hVU
  have hfU := hfT.mono_set (by norm_num : (1 : ℝ≥0∞) ≤ 2) hUH hUT'
  have hloc2 := localize_weak_divergence 2 isOpen_halfSpace hU B.a B.smooth_a
    hu3 hfU hψ hψc hψs (canonical_local_equation hUH hUT' hu2.memW1p hcan)
  have hw0 := memW01p_mul_smooth isOpen_halfSpace hu0 hψ hψc
  have hw3 := memWkp_mul_smooth_of_tsupport_subset 3 isOpen_halfSpace hU hu3 hψ hψc hψs
  have hw4 := flat_dirichlet_H4_of_weakEquation B hV hVc hw0 hw3.le_succ hloc2.1 hloc2.2
  apply (MemWkp_congr_ae (by norm_num) hVH (u := fun x => ψ x * u x) ?_).mp hw4
  filter_upwards [ae_restrict_mem hVH.measurableSet] with x hx
  rw [hψone x (subset_closure hx.1), one_mul]

#print axioms flat_local_H4_of_weakEquation
end Yamabe3.Analysis.UniformElliptic
