/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Geometry/CurveShortening/Comparison/AnnularEvolution/Plateau/Uniformization/Scalar/Regularity.lean

Retains the compact-test positivity argument and uses it to recover the classical
homogeneous Schrödinger equation.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.GreenCorrection
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.ClassicalEquation

/-!
# Native pointwise equations from smooth distributional representatives

The potential is an actual smooth function on the given Riemannian manifold.
The test equation uses its native Laplacian and volume. The proof localizes
the smooth representative with genuine manifold bump functions and tests
against the actual residual, using positive native volume on open sets.

This is a regularity-to-equation bridge, not a Green existence assertion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology

namespace Yamabe3.Analysis

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Formal self-adjointness for compact smooth functions uses the retained
native Laplacian, volume, and pointwise multiplication by the potential. -/
theorem native_schrodinger_integral_comm (D : LeviCivitaData g)
    {V f h : M → ℝ} (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h)
    (hfc : HasCompactSupport f) (hhc : HasCompactSupport h) :
    (∫ x, (-D.laplacian f x + V x * f x) * h x ∂g.volumeMeasure) =
      ∫ x, f x * (-D.laplacian h x + V x * h x) ∂g.volumeMeasure := by
  have h₁ : Integrable (fun x => h x * D.laplacian f x) g.volumeMeasure :=
    D.integrable_mul_laplacian hh hf hhc
  have h₂ : Integrable (fun x => f x * D.laplacian h x) g.volumeMeasure :=
    D.integrable_mul_laplacian hf hh hfc
  have h₃ : Integrable (fun x => V x * f x * h x) g.volumeMeasure :=
    ((hV.continuous.mul hf.continuous).mul hh.continuous).integrable_of_hasCompactSupport
      (hfc.mul_left.mul_right)
  calc
    _ = ∫ x, -(h x * D.laplacian f x) + V x * f x * h x ∂g.volumeMeasure := by
      congr 1
      funext x
      ring
    _ = -(∫ x, h x * D.laplacian f x ∂g.volumeMeasure) +
        ∫ x, V x * f x * h x ∂g.volumeMeasure := by
      simpa only [Pi.neg_apply, integral_neg] using integral_add h₁.neg h₃
    _ = -(∫ x, f x * D.laplacian h x ∂g.volumeMeasure) +
        ∫ x, V x * f x * h x ∂g.volumeMeasure := by
      rw [integral_mul_laplacian_comm_of_compact_tests hf hh hfc hhc]
    _ = ∫ x, -(f x * D.laplacian h x) + V x * f x * h x ∂g.volumeMeasure := by
      simpa only [Pi.neg_apply, integral_neg] using (integral_add h₂.neg h₃).symm
    _ = _ := by
      congr 1
      funext x
      ring

/-- Every smooth representative of the homogeneous native transposed
Schrödinger equation satisfies the actual pointwise differential equation.
No variational eigenfunction or sign condition on the potential is used. -/
theorem native_schrodinger_eq_zero_of_smooth_transposed
    (D : LeviCivitaData g) {Ω : Set M} (hΩ : IsOpen Ω)
    {V U : M → ℝ} (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V)
    (hU : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U Ω)
    (hweak : ∀ f : EnergyTest D Ω,
      (∫ y, (-D.laplacian f y + V y * f y) * U y ∂g.volumeMeasure) = 0) :
    ∀ x ∈ Ω, -D.laplacian U x + V x * U x = 0 := by
  intro x hx
  obtain ⟨H, hHs, hHc, -, hHU⟩ := exists_compact_smooth_germ hΩ hU hx
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) x).mem_iff.mp
    (inter_mem (hΩ.mem_nhds hx) hHU)
  let R : M → ℝ := fun y => -D.laplacian H y + V y * H y
  have hRs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ R :=
    (D.contMDiff_laplacian hHs).neg.add (hV.mul hHs)
  let f : EnergyTest D Ω := ⟨fun y => b y * R y,
    b.contMDiff.mul hRs, b.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans (fun y hy => (hb hy).1)⟩
  have htest : (∫ y, (-D.laplacian f y + V y * f y) * U y ∂g.volumeMeasure) =
      ∫ y, (-D.laplacian f y + V y * f y) * H y ∂g.volumeMeasure := by
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ tsupport (f : M → ℝ)
    · rw [(hb (tsupport_mul_subset_left hy)).2]
    · have hfy : f y = 0 := image_eq_zero_of_notMem_tsupport hy
      have hΔ : D.laplacian f y = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hy (D.tsupport_laplacian_subset f h))
      simp only [hfy, hΔ, neg_zero, mul_zero, add_zero, zero_mul]
  have hzero : (∫ y, b y * (R y * R y) ∂g.volumeMeasure) = 0 := by
    calc
      _ = ∫ y, f y * (-D.laplacian H y + V y * H y) ∂g.volumeMeasure := by
        congr 1
        funext y
        change b y * (R y * R y) = (b y * R y) * R y
        ring
      _ = ∫ y, (-D.laplacian f y + V y * f y) * H y ∂g.volumeMeasure :=
        (native_schrodinger_integral_comm D hV f.smooth hHs f.hasCompactSupport hHc).symm
      _ = 0 := htest.symm.trans (hweak f)
  have hRx : R x = 0 := by
    by_contra hRx
    let : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
    have hpos := integral_pos_of_integrable_nonneg_nonzero (μ := g.volumeMeasure)
      (b.continuous.mul (hRs.continuous.mul hRs.continuous))
      ((b.continuous.mul (hRs.continuous.mul hRs.continuous)).integrable_of_hasCompactSupport
        b.hasCompactSupport.mul_right)
      (fun y => mul_nonneg b.nonneg (mul_self_nonneg (R y)))
      (x := x) (by simpa only [Pi.mul_apply, b.eq_one, one_mul] using mul_ne_zero hRx hRx)
    exact hpos.ne' hzero
  have hLap := D.laplacian_eq_of_eventuallyEq hHU
  have hVal := hHU.eq_of_nhds
  dsimp only [R] at hRx
  simpa only [hLap, hVal] using hRx

/-- The normalized conformal Laplacian has the intended native pointwise
equation on every open region where its distributional representative is
smooth. The factor `1/8` is kept explicit. -/
theorem native_conformalLaplacian_eq_zero_of_smooth_transposed
    (D : LeviCivitaData g) {Ω : Set M} (hΩ : IsOpen Ω)
    {U : M → ℝ} (hU : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U Ω)
    (hweak : ∀ f : EnergyTest D Ω,
      (∫ y, (-D.laplacian f y + (D.scalarCurvature y / 8) * f y) * U y
        ∂g.volumeMeasure) = 0) :
    ∀ x ∈ Ω, -D.laplacian U x + (D.scalarCurvature x / 8) * U x = 0 := by
  apply native_schrodinger_eq_zero_of_smooth_transposed D hΩ
    (D.contMDiff_scalarCurvature.div_const 8) hU hweak

#print axioms native_schrodinger_integral_comm
#print axioms native_schrodinger_eq_zero_of_smooth_transposed
#print axioms native_conformalLaplacian_eq_zero_of_smooth_transposed

end Yamabe3.Analysis
