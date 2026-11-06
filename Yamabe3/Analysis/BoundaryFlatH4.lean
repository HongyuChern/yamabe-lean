/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Sobolev/Boundary/Regularity/Tangential.lean

Uses the weak equation restriction calculation in the flat boundary H4 argument.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.BoundaryNormalH4
import PoincareLib.Analysis.Sobolev.Boundary.H3
import PoincareLib.Analysis.Sobolev.Boundary.Localization.WeakEquation

/-!
# Genuine fourth-order regularity at a flat zero Dirichlet boundary

The actual compact cutoff commutator and tangential zero-boundary
approximation produce the tangential H3 inputs to normal recovery.
No H3 solution or tangential H3 hypothesis remains in the main H4 theorem.
This is membership regularity, not a uniform boundary norm estimate.
-/
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

private theorem zeroBoundary_congr {O : Set E} (hO : IsOpen O)
    {u v : E → ℝ} (h : u =ᵐ[volume.restrict O] v) (hu : MemW01p 2 u O) :
    MemW01p 2 v O := by
  obtain ⟨-, w, φ, hφ, hc, hs, hl, hd⟩ := hu
  let wv : MemW1pWitness 2 v O :=
    { memLp := (memLp_congr_ae h).mp w.memLp
      weakGrad := w.weakGrad
      weakGrad_component_memLp := w.weakGrad_component_memLp
      isWeakGrad := fun i => hasWeakPartialDeriv_congr_ae hO i h (w.isWeakGrad i) }
  refine ⟨wv.memW1p, wv, φ, hφ, hc, hs, ?_, hd⟩
  convert hl using 1
  funext n
  apply eLpNorm_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

private theorem principal_restrict_canonical
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
  have he := Poincare.Analysis.Elliptic.weakEquation_congr_restrict hs
    (a := a) (q := fun i => chosenWeakPartial' 2 i u O)
    (fun _ _ => rfl) (fun _ _ _ => rfl) heq φ hφ hc ht
  simp only [Finset.sum_mul] at he
  rw [← he]
  apply integral_congr_ae
  filter_upwards [eventually_all.mpr (fun j =>
    chosenWeakPartial'_mono_set_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2) hW hs hu j)] with x hx
  simp only [← hx]

private theorem cutoff_local_derivative_zeroBoundary
    {U : Set E} (hU : IsOpen U) {u χ : E → ℝ}
    (hu0 : MemW01p 2 u (halfSpace d)) (hu2 : MemWkp 2 2 u (halfSpace d))
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U)
    (k : Fin d) (hk : k ≠ 0) :
    MemW01p 2 (fun x => χ x * chosenWeakPartial' 2 k u (U ∩ halfSpace d) x)
      (halfSpace d) := by
  have hbase := memW01p_mul_chosenWeakPartial_tangential hu0 hu2 hχ hc k hk
  apply zeroBoundary_congr isOpen_halfSpace (u := fun x =>
    χ x * chosenWeakPartial' 2 k u (halfSpace d) x) _ hbase
  have hp := chosenWeakPartial'_mono_set_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (hU.inter isOpen_halfSpace) inter_subset_right hu2.memW1p k
  have hP : ∀ᵐ x ∂volume.restrict (halfSpace d), x ∈ U →
      chosenWeakPartial' 2 k u (halfSpace d) x =
        chosenWeakPartial' 2 k u (U ∩ halfSpace d) x :=
    (ae_restrict_iff' hU.measurableSet).mp
      (by rw [Measure.restrict_restrict hU.measurableSet]; exact hp)
  filter_upwards [hP] with x hx
  by_cases hxU : x ∈ U
  · rw [hx hxU]
  · rw [image_eq_zero_of_notMem_tsupport (fun ht => hxU (hs ht))]
    simp

private theorem flat_H4_of_global_H3
    (B : SmoothEllipticBilinearForm d univ)
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    {u f : E → ℝ} (hu0 : MemW01p 2 u (halfSpace d))
    (hu3 : MemWkp 3 2 u (halfSpace d)) (hf : MemWkp 2 2 f (halfSpace d))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfSpace d →
      (∫ x in halfSpace d, ∑ i, ∑ j, B.a x i j *
        chosenWeakPartial' 2 j u (halfSpace d) x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in halfSpace d, f x * φ x) :
    MemWkp 4 2 u (V ∩ halfSpace d) := by
  let H := halfSpace d
  obtain ⟨U, hU, hVU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hVc
  have hVH := hV.inter (isOpen_halfSpace (d := d))
  have hUH := hU.inter (isOpen_halfSpace (d := d))
  have hVU' : V ∩ H ⊆ U ∩ H := inter_subset_inter_left H (subset_closure.trans hVU)
  have hU3 := hu3.mono_set (by norm_num : (1 : ℝ≥0∞) ≤ 2) hUH inter_subset_right
  have hfU := hf.mono_set (by norm_num : (1 : ℝ≥0∞) ≤ 2) hUH inter_subset_right
  have heqU := principal_restrict_canonical hUH inter_subset_right hu3.memW1p heq
  obtain ⟨χ, hχ, hc, -, hone, hs⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff hVc hU hVU
  apply memWkp_four_of_tangential_memWkp_three B hVH
    (hVc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left))
    (hu3.mono_set (by norm_num) hVH inter_subset_right)
    (hf.mono_set (by norm_num) hVH inter_subset_right) _ 
    (principal_restrict_canonical hVH inter_subset_right hu3.memW1p heq)
  intro k hk
  let p := chosenWeakPartial' 2 k u (U ∩ H)
  obtain ⟨F, hF, hFeq⟩ := exists_differentiated_sobolev_source 1 hUH
    (hUc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left))
    B.a B.smooth_a hU3 hfU heqU k
  have hp : MemWkp 2 2 p (U ∩ H) := hU3.chosenWeakPartial_mem k
  have hlocal := localize_weak_divergence 1 isOpen_halfSpace hU B.a B.smooth_a
    hp hF hχ hc hs hFeq
  have hv0 : MemW01p 2 (fun x => χ x * p x) H :=
    cutoff_local_derivative_zeroBoundary hU hu0 hu3.le_succ hχ hc hs k hk
  have hv2 : MemWkp 2 2 (fun x => χ x * p x) H :=
    memWkp_mul_smooth_of_tsupport_subset 2 isOpen_halfSpace hU hp hχ hc hs
  have hv3 := memWkp_three_of_weakEquation B hV hVc hv0 hv2 hlocal.1.memW1p hlocal.2
  apply (MemWkp_congr_ae (by norm_num) hVH
    (u := fun x => χ x * p x) (v := chosenWeakPartial' 2 k u (V ∩ H)) ?_).mp hv3
  filter_upwards [chosenWeakPartial'_mono_set_ae
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hVH hVU' hU3.memW1p k,
    ae_restrict_mem hVH.measurableSet] with x hx hxV
  change χ x * chosenWeakPartial' 2 k u (U ∩ H) x = _
  rw [hone x (subset_closure hxV.1), one_mul, hx]

/-- Genuine H4 at every compact part of the flat Dirichlet boundary,
starting from the original H2 weak solution and its H2 source. H3 and
tangential H3 are produced internally. No fourth-order boundary condition
or pre-existing H4 solution is supplied. -/
theorem flat_dirichlet_H4_of_weakEquation
    (B : SmoothEllipticBilinearForm d univ)
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    {u f : E → ℝ} (hu0 : MemW01p 2 u (halfSpace d))
    (hu2 : MemWkp 2 2 u (halfSpace d)) (hf : MemWkp 2 2 f (halfSpace d))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfSpace d →
      (∫ x in halfSpace d, ∑ i, ∑ j, B.a x i j *
        chosenWeakPartial' 2 j u (halfSpace d) x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in halfSpace d, f x * φ x) :
    MemWkp 4 2 u (V ∩ halfSpace d) := by
  let H := halfSpace d
  obtain ⟨U, hU, hVU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hVc
  have hVH := hV.inter (isOpen_halfSpace (d := d))
  have hUH := hU.inter (isOpen_halfSpace (d := d))
  have hu3 : MemWkp 3 2 u (U ∩ H) :=
    memWkp_three_of_weakEquation B hU hUc hu0 hu2 hf.memW1p heq
  obtain ⟨χ, hχ, hc, -, hone, hs⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff hVc hU hVU
  have hfU := hf.mono_set (by norm_num : (1 : ℝ≥0∞) ≤ 2) hUH inter_subset_right
  have hlocal := localize_weak_divergence 2 isOpen_halfSpace hU B.a B.smooth_a
    hu3 hfU hχ hc hs
      (principal_restrict_canonical hUH inter_subset_right hu2.memW1p heq)
  have hv0 : MemW01p 2 (fun x => χ x * u x) H :=
    memW01p_mul_smooth isOpen_halfSpace hu0 hχ hc
  have hv3 : MemWkp 3 2 (fun x => χ x * u x) H :=
    memWkp_mul_smooth_of_tsupport_subset 3 isOpen_halfSpace hU hu3 hχ hc hs
  have hv4 := flat_H4_of_global_H3 B hV hVc hv0 hv3 hlocal.1 hlocal.2
  apply (MemWkp_congr_ae (by norm_num) hVH
    (u := fun x => χ x * u x) (v := u) ?_).mp hv4
  filter_upwards [ae_restrict_mem hVH.measurableSet] with x hx
  rw [hone x (subset_closure hx.1), one_mul]

#print axioms flat_dirichlet_H4_of_weakEquation
end Yamabe3.Analysis.UniformElliptic

