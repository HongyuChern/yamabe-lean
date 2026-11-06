/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Geometry/Riemannian/Elliptic/Dirichlet/ClassicalEquation.lean

Uses the compact-test positivity argument in the classical equation with smooth forcing.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.GreenClassical

/-!
# The actual local forced equation for the same smooth representative

The source term is retained in the native transposed equation. A compact
smooth germ and a genuine smooth bump test the local residual. Native
positive volume turns the resulting integral of a nonnegative square into
the original pointwise equation. No global smoothness of the solution, sign
condition on the potential, or boundary integration formula is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Local native distributional equality with a smooth source implies the
pointwise forced equation of the same smooth function. -/
theorem native_schrodinger_eq_source_of_smooth_transposed
    (D : LeviCivitaData g) {Ω : Set M} (hΩ : IsOpen Ω)
    {V F U : M → ℝ}
    (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V)
    (hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F)
    (hU : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U Ω)
    (hweak : ∀ f : EnergyTest D Ω,
      (∫ y, (-D.laplacian f y + V y * f y) * U y ∂g.volumeMeasure) =
        ∫ y, f y * F y ∂g.volumeMeasure) :
    ∀ x ∈ Ω, -D.laplacian U x + V x * U x = F x := by
  intro x hx
  obtain ⟨H, hHs, hHc, -, hHU⟩ := exists_compact_smooth_germ hΩ hU hx
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) x).mem_iff.mp
    (inter_mem (hΩ.mem_nhds hx) hHU)
  let R : M → ℝ := fun y => -D.laplacian H y + V y * H y - F y
  have hRs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ R :=
    ((D.contMDiff_laplacian hHs).neg.add (hV.mul hHs)).sub hF
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
  have hiL : Integrable (fun y => f y * (-D.laplacian H y + V y * H y))
      g.volumeMeasure :=
    (f.smooth.continuous.mul
      ((D.contMDiff_laplacian hHs).neg.add (hV.mul hHs)).continuous).integrable_of_hasCompactSupport
        f.hasCompactSupport.mul_right
  have hiF : Integrable (fun y => f y * F y) g.volumeMeasure :=
    (f.smooth.continuous.mul hF.continuous).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
  have hzero : (∫ y, b y * (R y * R y) ∂g.volumeMeasure) = 0 := by
    calc
      _ = (∫ y, f y * (-D.laplacian H y + V y * H y) ∂g.volumeMeasure) -
          ∫ y, f y * F y ∂g.volumeMeasure := by
        rw [← integral_sub hiL hiF]
        congr 1
        funext y
        change b y * (R y * R y) =
          (b y * R y) * (-D.laplacian H y + V y * H y) - (b y * R y) * F y
        dsimp only [R]
        ring
      _ = (∫ y, (-D.laplacian f y + V y * f y) * H y ∂g.volumeMeasure) -
          ∫ y, f y * F y ∂g.volumeMeasure := by
        rw [native_schrodinger_integral_comm D hV f.smooth hHs f.hasCompactSupport hHc]
      _ = 0 := by rw [← htest, hweak f, sub_self]
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
  apply sub_eq_zero.mp
  dsimp only [R] at hRx
  simpa only [hLap, hVal] using hRx

#print axioms native_schrodinger_eq_source_of_smooth_transposed

end Yamabe3.Analysis
