/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Elliptic/Regularity/InteriorEstimates/Embedding/Compact.lean
  PoincareLib/Analysis/Elliptic/Regularity/InteriorEstimates/Embedding/Ball.lean

Adapts the cutoff and finite-cover proof to the three-dimensional H2 embedding and the
explicit W2,2 to W1,6 step.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.UniformElliptic.LocalUniformJet
import PoincareLib.Analysis.Elliptic.Regularity.InteriorEstimates.Embedding.Cutoff
import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Embedding.ExponentIteration

/-!
# Quantitative H2 to C0 embedding in actual three-dimensional Euclidean space

A fixed compact cutoff, the proved quantitative W2,2 to W1,6 step, and the
actual uniform Morrey inequality give one constant before the smooth function.
Only two actual L2 derivatives are used. No regularity constant chosen after
the function is promoted to a uniform estimate.
The cutoff/profile and finite-cover proof is adapted from fixed upstream
InteriorEstimates/Embedding/{Ball,Compact} at Poincare commit
62db01af9388dc1d9b56b66d6674f4c09b2318a2 (Apache-2.0); the exponent
step is specialized to the actual three-dimensional W2,2 to W1,6 estimate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set MeasureTheory Filter Metric
open scoped ENNReal ContDiff Topology

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding
open Poincare.Analysis.Elliptic.InteriorEstimates

local notation "E" => EuclideanSpace ℝ (Fin 3)

/-- A genuine quantitative three-dimensional H2 embedding, with a constant
chosen before the function and the evaluation point. -/
theorem exists_h2_sup_bound_on_ball {x₀ : E} {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : E → ℝ}, ContDiff ℝ ∞ u →
      ∀ x ∈ ball x₀ (R / 2),
        ‖u x‖ ≤ C * (derivativeProfile 2 (ball x₀ R) 2 u).toReal := by
  classical
  let Ω := ball x₀ R
  obtain ⟨χ, A, hχ, hχc, hχs, hχone, hA, hcutoff⟩ :=
    exists_fixed_cutoff_profile_bound hR 2
  obtain ⟨B, hB, hmorrey⟩ :=
    Poincare.Analysis.Sobolev.EuclideanMorrey.smooth_morrey_iteratedFDeriv_bound_uniform
      (d := 3) (p := 6) (by norm_num) hR 0
  let T := TowerStep.subcriticalConstant 1 3 2
  let N : ℝ≥0∞ := ∑ j ∈ Finset.range (2 + 1), (Fintype.card (Fin j → Fin 3) : ℝ≥0∞)
  let Q : ℝ≥0∞ := ENNReal.ofReal T * N * ENNReal.ofReal A
  have hN : N ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.natCast_ne_top _)
  have hQ : Q ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN) ENNReal.ofReal_ne_top
  refine ⟨B * Q.toReal, mul_nonneg hB ENNReal.toReal_nonneg, ?_⟩
  intro u hu x hx
  let w : E → ℝ := fun y => χ y * u y
  have hw : ContDiff ℝ ∞ w := hχ.mul hu
  have hwc : HasCompactSupport w := hχc.mul_right
  have hws : tsupport w ⊆ Ω := tsupport_mul_subset_left.trans hχs
  have hw2 : MemWkp 2 2 w Ω :=
    MemWkp_of_smooth_compactSupport isOpen_ball hw hwc hws (by norm_num) 2
  have htower := TowerStep.MemWkp_subcritical_iterated (d := 3) 1
    (p := 2) (by norm_num) (by norm_num) isOpen_ball hwc hws (by norm_num; exact hw2)
  have hnorm : iteratedWeakSobolevNorm 1 6 w Ω ≤
      ENNReal.ofReal T * iteratedWeakSobolevNorm 2 2 w Ω := by
    simpa only [TowerStep.pOne, Nat.cast_ofNat, show (3 : ℝ) - 2 = 1 by norm_num,
      div_one, show (3 : ℝ) * 2 = 6 by norm_num, ENNReal.ofReal_ofNat] using htower.2
  have hprofile : derivativeProfile 6 Ω 1 w ≤ Q * derivativeProfile 2 Ω 2 u := by
    calc
      _ ≤ iteratedWeakSobolevNorm 1 6 w Ω :=
        eLpNorm_iteratedFDeriv_le_wkpNorm isOpen_ball (by norm_num) 1 hw hwc hws
      _ ≤ ENNReal.ofReal T * iteratedWeakSobolevNorm 2 2 w Ω := hnorm
      _ ≤ ENNReal.ofReal T * (N * derivativeProfile 2 Ω 2 w) := by
        gcongr
        exact wkpNorm_le_derivativeProfile isOpen_ball (by norm_num) 2 hw hwc hws
      _ ≤ ENNReal.ofReal T * (N * (ENNReal.ofReal A * derivativeProfile 2 Ω 2 u)) := by
        gcongr
        exact hcutoff hu
      _ = _ := by dsimp [Q]; ring
  have hfinite : derivativeProfile 2 Ω 2 u ≠ ⊤ := by
    simpa using derivativeProfile_ne_top (by norm_num : (0 : ℝ) < 2) hR 2 hu
  have hprofileReal : (derivativeProfile 6 Ω 1 w).toReal ≤
      Q.toReal * (derivativeProfile 2 Ω 2 u).toReal := by
    simpa only [ENNReal.toReal_mul] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top hQ hfinite) hprofile
  have hsum : (derivativeProfile 6 Ω 1 w).toReal =
      ∑ j ∈ Finset.range 2,
        (eLpNorm (fun y => ‖iteratedFDeriv ℝ j w y‖) 6 (volume.restrict Ω)).toReal := by
    apply ENNReal.toReal_sum
    intro j hj
    have hfinite6 : derivativeProfile 6 Ω 1 w ≠ ⊤ := by
      simpa only [ENNReal.ofReal_ofNat] using
        derivativeProfile_ne_top (x₀ := x₀) (by norm_num : (0 : ℝ) < 6) hR 1 hw
    exact (ENNReal.lt_top_of_sum_ne_top (s := Finset.range 2)
      (f := fun j => eLpNorm (fun y => ‖iteratedFDeriv ℝ j w y‖) 6 (volume.restrict Ω))
      hfinite6 hj).ne
  have hm := hmorrey hw x hx
  norm_num only [Nat.zero_add, norm_iteratedFDeriv_zero, ENNReal.ofReal_ofNat] at hm
  rw [← hsum] at hm
  have hwx : w x = u x := by dsimp only [w]; rw [hχone hx, one_mul]
  rw [hwx] at hm
  exact hm.trans ((mul_le_mul_of_nonneg_left hprofileReal hB).trans_eq (mul_assoc _ _ _).symm)

/-- The actual H2 estimate is uniform on any fixed compact subset of an
open precompact set. Finite subcover constants are chosen before u. -/
theorem exists_h2_sup_bound_on_compact {K V : Set E}
    (hK : IsCompact K) (hV : IsOpen V) (hVc : IsCompact (closure V)) (hKV : K ⊆ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : E → ℝ}, ContDiff ℝ ∞ u →
      ∀ x ∈ K, ‖u x‖ ≤ C * (derivativeProfile 2 V 2 u).toReal := by
  classical
  have hballs : ∀ x : K, ∃ R : ℝ, 0 < R ∧ ball (x : E) R ⊆ V := by
    intro x
    exact Metric.isOpen_iff.mp hV x (hKV x.property)
  choose R hR hRV using hballs
  choose A hA hbound using fun x : K => exists_h2_sup_bound_on_ball (hR x)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => ball (x : E) (R x / 2))
    (fun _ => isOpen_ball) (fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (half_pos (hR ⟨x, hx⟩))⟩)
  have hsnonneg : 0 ≤ ∑ x ∈ s, A x := Finset.sum_nonneg (fun x _ => hA x)
  refine ⟨1 + ∑ x ∈ s, A x, add_pos_of_pos_of_nonneg zero_lt_one hsnonneg, ?_⟩
  intro u hu x hx
  obtain ⟨y, hys, hxy⟩ := mem_iUnion₂.mp (hs hx)
  have hprofile : (derivativeProfile 2 (ball (y : E) (R y)) 2 u).toReal ≤
      (derivativeProfile 2 V 2 u).toReal :=
    ENNReal.toReal_mono (derivativeProfile_ne_top_on_precompact hVc _ hu)
      (derivativeProfile_mono_set (hRV y) 2 _ u)
  apply (hbound y hu x hxy).trans
  apply mul_le_mul
  · exact (Finset.single_le_sum (fun z hz => hA z) hys).trans (le_add_of_nonneg_left zero_le_one)
  · exact hprofile
  · exact ENNReal.toReal_nonneg
  · exact add_nonneg zero_le_one hsnonneg

#print axioms exists_h2_sup_bound_on_ball
#print axioms exists_h2_sup_bound_on_compact

end Yamabe3.Analysis.UniformElliptic
