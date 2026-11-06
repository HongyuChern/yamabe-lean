/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Sobolev/Boundary/Regularity/Tangential.lean

Re-exposes the local equation restriction calculation from BoundaryFlatH4 as a public
interface for quantitative localization.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.BoundaryLocalH4

/-! Public quantitative-localization adapters. These three proofs are exact
adaptations of the private S014 BoundaryFlatH4 helpers, with names exposed
for the norm-estimate assembly. No historical source is edited. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.BoundaryTangential
open Poincare.Analysis.Sobolev.BoundaryLocalization
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem localized_zeroBoundary_congr {O : Set E} (hO : IsOpen O)
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

theorem localized_principal_restrict_canonical
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

theorem localized_tangential_derivative_zeroBoundary
    {U : Set E} (hU : IsOpen U) {u χ : E → ℝ}
    (hu0 : MemW01p 2 u (halfSpace d)) (hu2 : MemWkp 2 2 u (halfSpace d))
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U)
    (k : Fin d) (hk : k ≠ 0) :
    MemW01p 2 (fun x => χ x * chosenWeakPartial' 2 k u (U ∩ halfSpace d) x)
      (halfSpace d) := by
  have hbase := memW01p_mul_chosenWeakPartial_tangential hu0 hu2 hχ hc k hk
  apply localized_zeroBoundary_congr isOpen_halfSpace (u := fun x =>
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

#print axioms localized_zeroBoundary_congr
#print axioms localized_principal_restrict_canonical
#print axioms localized_tangential_derivative_zeroBoundary
end Yamabe3.Analysis.UniformElliptic
