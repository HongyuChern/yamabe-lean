/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Elliptic/Regularity/GradientCompactness/LocalL2.lean

Uses the square-distance identity for actual L2 limits in the weak first-derivative
construction.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.UniformElliptic.LocalCaccioppoli
import PoincareLib.Analysis.Elliptic.Regularity.WeakDerivativeLimit

/-!
# Genuine weak first derivatives from smooth spectral energy bounds

Strong convergence is measured by actual Euclidean square integrals. The
classical derivatives of the locally smooth approximants are actual L2
functions, supplied by constructed smooth extensions. Their uniform energy
bound and the pinned Hahn--Banach/Riesz weak-derivative limit construct the
weak derivatives of the same L2 limit. No H1 certificate is an input.

The elementary L2 square identity follows the proof in pinned
GradientCompactness/LocalL2.lean (Apache-2.0); the upstream file is unchanged.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic

theorem norm_toLp_sq_eq_integral_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem norm_toLp_sub_sq_eq_integral_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, (f x - g x) ^ 2 ∂μ := by
  rw [← MemLp.toLp_sub hf hg]
  exact norm_toLp_sq_eq_integral_sq (hf.sub hg)

theorem tendsto_toLp_of_integral_sq_sub {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {uSeq : ℕ → X → ℝ} {u : X → ℝ}
    (hs : ∀ n, MemLp (uSeq n) 2 μ) (hu : MemLp u 2 μ)
    (hlim : Tendsto (fun n => ∫ x, (uSeq n x - u x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => (hs n).toLp (uSeq n)) atTop (𝓝 (hu.toLp u)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 (ε ^ 2) (sq_pos_of_pos hε)] with n hn
  rw [dist_eq_norm]
  have hsquare := norm_toLp_sub_sq_eq_integral_sq (hs n) hu
  nlinarith [norm_nonneg ((hs n).toLp (uSeq n) - hu.toLp u)]

/-- Actual local smoothness, actual square-integral convergence, and an
actual common gradient-energy bound construct all L2 weak partials of the
same function. No convergence of the derivatives is assumed. -/
theorem exists_weak_partials_of_local_smooth_approximation
    {d : ℕ} {O W : Set (EuclideanSpace ℝ (Fin d))}
    (hO : IsOpen O) (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWO : closure W ⊆ O)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : MemLp u 2 (volume.restrict W))
    (uSeq : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hsmooth : ∀ n, ContDiffOn ℝ ∞ (uSeq n) O)
    (hlim : Tendsto (fun n => ∫ x in W, (uSeq n x - u x) ^ 2) atTop (𝓝 0))
    {K : ℝ} (hK : 0 ≤ K)
    (hgrad : ∀ n, (∫ x in W, ∑ i : Fin d,
      (fderiv ℝ (uSeq n) x (EuclideanSpace.single i 1)) ^ 2) ≤ K) :
    ∃ du : Fin d → Lp ℝ 2 (volume.restrict W),
      (∀ i, ‖du i‖ ≤ Real.sqrt K) ∧
      ∀ i (φ : EuclideanSpace ℝ (Fin d) → ℝ),
        ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W →
        (∫ x in W, u x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          -(∫ x in W, du i x * φ x) := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  have hum (n : ℕ) : MemLp (uSeq n) 2 (volume.restrict W) :=
    memLp_of_local_smooth_precompact hO hW.measurableSet hWc hWO (hsmooth n)
  have hdm (n : ℕ) (i : Fin d) :
      MemLp (fun x => fderiv ℝ (uSeq n) x (EuclideanSpace.single i 1))
        2 (volume.restrict W) :=
    memLp_partial_of_local_smooth_precompact hO hW.measurableSet hWc hWO
      (hsmooth n) (EuclideanSpace.single i 1)
  have hseq := tendsto_toLp_of_integral_sq_sub hum hu hlim
  have hi (i : Fin d) : ∃ g : Lp ℝ 2 (volume.restrict W), ‖g‖ ≤ Real.sqrt K ∧
      ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W →
        (∫ x in W, hu.toLp u x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          -(∫ x in W, g x * φ x) := by
    let vSeq : ℕ → Lp ℝ 2 (volume.restrict W) := fun n => (hdm n i).toLp _
    have hvn (n : ℕ) : ‖vSeq n‖ ≤ Real.sqrt K := by
      have hb : (∫ x in W, (fderiv ℝ (uSeq n) x (EuclideanSpace.single i 1)) ^ 2) ≤ K := by
        apply le_trans ?_ (hgrad n)
        apply integral_mono (hdm n i).integrable_sq
          (integrable_finsetSum _ (fun j _ => (hdm n j).integrable_sq))
        intro x
        exact Finset.single_le_sum (fun j _ =>
          sq_nonneg (fderiv ℝ (uSeq n) x (EuclideanSpace.single j 1))) (Finset.mem_univ i)
      have hn : ‖vSeq n‖ ^ 2 =
          ∫ x in W, (fderiv ℝ (uSeq n) x (EuclideanSpace.single i 1)) ^ 2 :=
        norm_toLp_sq_eq_integral_sq (hdm n i)
      nlinarith [Real.sq_sqrt hK, Real.sqrt_nonneg K, norm_nonneg (vSeq n)]
    apply exists_weak_partial_of_bounded_approximation hseq
      (EuclideanSpace.single i 1) (Real.sqrt_nonneg K) hvn
    intro n φ hφ hc hs
    calc
      (∫ x in W, (hum n).toLp (uSeq n) x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          ∫ x in W, uSeq n x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
        apply integral_congr_ae
        filter_upwards [(hum n).coeFn_toLp] with x hx
        rw [hx]
      _ = -(∫ x in W, fderiv ℝ (uSeq n) x (EuclideanSpace.single i 1) * φ x) :=
        integral_mul_partial_test hW
          ((hsmooth n).mono (subset_closure.trans hWO)) (EuclideanSpace.single i 1) hφ hc hs
      _ = -(∫ x in W, vSeq n x * φ x) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [(hdm n i).coeFn_toLp] with x hx
        rw [show vSeq n x = fderiv ℝ (uSeq n) x (EuclideanSpace.single i 1) from hx]
  choose du hdu hweak using hi
  refine ⟨du, hdu, fun i φ hφ hc hs => ?_⟩
  calc
    (∫ x in W, u x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in W, hu.toLp u x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      filter_upwards [hu.coeFn_toLp] with x hx
      rw [hx]
    _ = _ := hweak i φ hφ hc hs

#print axioms tendsto_toLp_of_integral_sq_sub
#print axioms exists_weak_partials_of_local_smooth_approximation

end Yamabe3.Analysis.UniformElliptic
