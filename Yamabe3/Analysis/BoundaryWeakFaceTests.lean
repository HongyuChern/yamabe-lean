/-
Copyright (c) 2026 The PoincareLib contributors.
Copyright 2026 The DifferentialGeometry contributors
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Analysis/Sobolev/Boundary/Extension/Reflection.lean
Earlier source credited by PoincareLib at DifferentialGeometry 1b535dd102b94cc42b107cca27059687888f08b3.
  DifferentialGeometry/Analysis/Sobolev/WithBoundary/Embedding/EvenReflectionExtension.lean

Extracts the weak face test arguments into local helpers and exposes the test interface
with normal vanishing.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.BoundaryNormalScaling

/-! Weak tests reaching the flat face, with the exact vanishing condition
in the normal direction. Adapted verbatim in proof content from fixed
PoincareLib Analysis/Sobolev/Boundary/Extension/Reflection.lean,
commit 62db01af9388dc1d9b56b66d6674f4c09b2318a2, to expose the necessary
interface without changing the dependency. Its source attributes the
reflection construction to Chow--Liao--Qin revision
1b535dd102b94cc42b107cca27059687888f08b3, Apache-2.0.
This does not assert arbitrary nonzero boundary test admissibility. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set MeasureTheory Filter
open scoped Topology ENNReal ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.BoundaryTangential
open Poincare.Analysis.Sobolev.BoundaryExtension
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem weakPartial_test_limit
    {p : ℝ≥0∞} (hp : 1 ≤ p) {u g ψ : E → ℝ} (i : Fin d)
    (hu : MemLp u p (volume.restrict (halfSpace d)))
    (hg : MemLp g p (volume.restrict (halfSpace d)))
    (hw : HasWeakPartialDeriv i g u (halfSpace d))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (θ : ℕ → E → ℝ) (hs : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (θ n))
    (hθc : ∀ n, tsupport (θ n) ⊆ halfSpace d)
    (hnorm : ∀ n x, ‖θ n x‖ ≤ 1)
    (hlim : ∀ x ∈ halfSpace d, Tendsto (fun n => θ n x) atTop (𝓝 1))
    (herr : Tendsto (fun n => ∫ x in halfSpace d,
      u x * ψ x * fderiv ℝ (θ n) x (EuclideanSpace.single i 1)) atTop (𝓝 0)) :
    (∫ x in halfSpace d, u x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) =
      -(∫ x in halfSpace d, g x * ψ x) := by
  let dψ : E → ℝ := fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1)
  have hdc : Continuous dψ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds : HasCompactSupport dψ := hc.fderiv_apply (𝕜 := ℝ) _
  have hdint : Integrable (fun x => u x * dψ x) (volume.restrict (halfSpace d)) :=
    hu.locallyIntegrable hp |>.integrable_smul_right_of_hasCompactSupport hdc hds
  have hgint : Integrable (fun x => g x * ψ x) (volume.restrict (halfSpace d)) :=
    hg.locallyIntegrable hp |>.integrable_smul_right_of_hasCompactSupport hψ.continuous hc
  have hlimit {a : E → ℝ} (ha : Integrable a (volume.restrict (halfSpace d))) :
      Tendsto (fun n => ∫ x in halfSpace d, θ n x * a x) atTop
        (𝓝 (∫ x in halfSpace d, a x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖a x‖)
    · intro n
      exact ((hs n).continuous.aestronglyMeasurable.restrict).mul ha.aestronglyMeasurable
    · exact ha.norm
    · intro n
      exact Eventually.of_forall fun x => by
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (hnorm n x) (norm_nonneg _)).trans_eq (one_mul _)
    · filter_upwards [ae_restrict_mem isOpen_halfSpace.measurableSet] with x hx
      simpa using (hlim x hx).mul_const (a x)
  have heq (n : ℕ) :
      (∫ x in halfSpace d, θ n x * (u x * dψ x)) +
        (∫ x in halfSpace d, u x * ψ x * fderiv ℝ (θ n) x (EuclideanSpace.single i 1)) =
      -(∫ x in halfSpace d, θ n x * (g x * ψ x)) := by
    have ha : Integrable (fun x => θ n x * (u x * dψ x))
        (volume.restrict (halfSpace d)) := by
      convert hu.locallyIntegrable hp |>.integrable_smul_right_of_hasCompactSupport
        ((hs n).continuous.mul hdc) hds.mul_left using 1
      ext x
      simp only [smul_eq_mul, Pi.mul_apply]
      ring
    have hb : Integrable
        (fun x => u x * ψ x * fderiv ℝ (θ n) x (EuclideanSpace.single i 1))
        (volume.restrict (halfSpace d)) := by
      convert hu.locallyIntegrable hp |>.integrable_smul_right_of_hasCompactSupport
        (hψ.continuous.mul ((hs n).continuous_fderiv (by simp) |>.clm_apply
          (continuous_const (y := EuclideanSpace.single i 1))))
        hc.mul_right using 1
      ext x
      simp only [smul_eq_mul, Pi.mul_apply]
      ring
    rw [← integral_add ha hb]
    have hprod (x : E) :
        fderiv ℝ (fun y => θ n y * ψ y) x (EuclideanSpace.single i 1) =
          θ n x * dψ x + ψ x * fderiv ℝ (θ n) x (EuclideanSpace.single i 1) := by
      have hd := (((hs n).differentiable (by simp) x).hasFDerivAt.mul
        (hψ.differentiable (by simp) x).hasFDerivAt).fderiv
      have h := congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hd
      simpa [dψ, Pi.mul_def] using h
    calc
      _ = ∫ x in halfSpace d, u x * fderiv ℝ (fun y => θ n y * ψ y) x
          (EuclideanSpace.single i 1) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by dsimp only; rw [hprod]; ring
      _ = _ := hw _ ((hs n).mul hψ) hc.mul_left (tsupport_mul_subset_left.trans (hθc n))
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
  have hh := (hlimit hdint).add herr
  simpa only [add_zero] using tendsto_nhds_unique hh
    ((hlimit hgint).neg.congr' (Eventually.of_forall fun n => (heq n).symm))

private theorem normalCutoff_error_tendsto {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u ψ : E → ℝ} (hu : MemLp u p (volume.restrict (halfSpace d)))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hface : ∀ x : E, x 0 = 0 → ψ x = 0) :
    Tendsto (fun n => ∫ x in halfSpace d,
      u x * ψ x * fderiv ℝ (normalCutoff n) x (EuclideanSpace.single 0 1)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hψbound⟩ := exists_norm_le_normalCoord hψ hc hface
  obtain ⟨D, hD, hθbound⟩ := exists_normalCutoff_normal_bound (d := d)
  have hI : Integrable ((tsupport ψ).indicator (fun x => ‖u x‖))
      (volume.restrict (halfSpace d)) :=
    (integrable_indicator_iff (isClosed_tsupport ψ).measurableSet).mpr
      ((hu.locallyIntegrable hp).integrableOn_isCompact hc).norm
  have h := tendsto_integral_of_dominated_convergence
    (fun x => C * D * (tsupport ψ).indicator (fun y => ‖u y‖) x)
    (μ := volume.restrict (halfSpace d))
    (F := fun n x => u x * ψ x *
      fderiv ℝ (normalCutoff n) x (EuclideanSpace.single 0 1))
    (f := fun _ => (0 : ℝ)) ?_ (hI.const_mul (C * D)) ?_ ?_
  · simpa using h
  · intro n
    exact (hu.1.mul hψ.continuous.aestronglyMeasurable.restrict).mul
      (((normalCutoff_smooth n).continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable.restrict
  · intro n
    filter_upwards [ae_restrict_mem isOpen_halfSpace.measurableSet] with x hx
    by_cases hs : x ∈ tsupport ψ
    · rw [indicator_of_mem hs, norm_mul, norm_mul]
      have hxb : ‖ψ x‖ * ‖fderiv ℝ (normalCutoff n) x (EuclideanSpace.single 0 1)‖ ≤ C * D := by
        calc
          _ ≤ (C * x 0) * ‖fderiv ℝ (normalCutoff n) x (EuclideanSpace.single 0 1)‖ :=
            mul_le_mul_of_nonneg_right (hψbound x hx.le) (norm_nonneg _)
          _ = C * (x 0 * ‖fderiv ℝ (normalCutoff n) x (EuclideanSpace.single 0 1)‖) := by ring
          _ ≤ C * D := mul_le_mul_of_nonneg_left (hθbound n x hx.le) hC
      nlinarith [norm_nonneg (u x)]
    · simp [indicator_of_notMem hs, image_eq_zero_of_notMem_tsupport hs]
  · filter_upwards [ae_restrict_mem isOpen_halfSpace.measurableSet] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [normalCutoff_fderiv_eventually_eq_zero hx] with n hn
    simp [hn]

theorem weakPartial_test_upToBoundary
    {p : ℝ≥0∞} (hp : 1 ≤ p) {u g ψ : E → ℝ} (i : Fin d)
    (hu : MemLp u p (volume.restrict (halfSpace d)))
    (hg : MemLp g p (volume.restrict (halfSpace d)))
    (hw : HasWeakPartialDeriv i g u (halfSpace d))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hface : i = 0 → ∀ x : E, x 0 = 0 → ψ x = 0) :
    (∫ x in halfSpace d, u x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) =
      -(∫ x in halfSpace d, g x * ψ x) := by
  apply weakPartial_test_limit hp i hu hg hw hψ hc normalCutoff normalCutoff_smooth
    normalCutoff_tsupport normalCutoff_norm_le (fun _ hx => normalCutoff_tendsto hx)
  by_cases hi : i = 0
  · subst i
    exact normalCutoff_error_tendsto hp hu hψ hc (hface rfl)
  · simp [normalCutoff_partial _ _ hi]


#print axioms weakPartial_test_upToBoundary
end Yamabe3.Analysis.UniformElliptic
