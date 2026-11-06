/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Geometry/Riemannian/Coordinates/Harmonic/SmoothReplacement.lean
  PoincareLib/Geometry/Riemannian/Elliptic/Dirichlet/InteriorRegularity.lean

Retains the chart ellipticity calculation and uses it in regularity for the smooth
forced equation.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.NativeForcedCoordinates
import Yamabe3.Analysis.NativeForcedSmoothBootstrap

/-!
# Smooth representatives for the native forced equation

Actual coordinate energy derivatives, positive definite metric coefficients,
and the metric density reduce the native transposed equation to the proved
inhomogeneous bootstrap. Local representatives are glued using native volume.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] {g : RiemannianMetric n M} {D : LeviCivitaData g}

theorem exists_smooth_representative_of_native_smooth_forced
    (hn : 0 < n) {Ω : Set M} (hΩ : IsOpen Ω)
    (V F : M → ℝ)
    (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V)
    (hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F)
    (w : H1Zero D univ)
    (hweak : ∀ f : EnergyTest D univ, tsupport (f : M → ℝ) ⊆ Ω →
      (∫ y, (-D.laplacian f y + V y * f y) * toL2 D univ w y ∂g.volumeMeasure) =
        ∫ y, f y * F y ∂g.volumeMeasure) :
    ∃ U : M → ℝ, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U Ω ∧
      U =ᵐ[g.volumeMeasure.restrict Ω] (toL2 D univ w : M → ℝ) := by
  apply exists_smooth_representative_of_local hΩ (toL2 D univ w)
  intro x hx
  obtain ⟨e, he, hei, K, hK, hKs, O, hO, hOK, hxO, hOΩ, -⟩ :=
    exists_precompact_coordinate_neighborhood (n := n) hΩ hx
  have hOs := hOK.trans hKs
  let p (i : Fin n) := localCoordinateDerivative (D := D) (Ω := univ)
    e he hei hK hKs hOK (EuclideanSpace.single i 1) w
  have huL2 := (g.memLp_pullback_on_compact e he hei (toL2 D univ w) hK hKs).mono_measure
    (Measure.restrict_mono hOK le_rfl)
  have hρ : ContDiffOn ℝ ∞ (g.pullbackVolumeDensity e) O := by
    intro y hy
    have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
      ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds (hOs hy)))
      (hD.mfderiv_injective (hOs hy))).1.contDiffWithinAt
  obtain ⟨U, hUs, hUae⟩ : ∃ U : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ ∞ U O ∧ U =ᵐ[volume.restrict O] (fun y => toL2 D univ w (e y)) := by
    apply UniformElliptic.exists_smooth_representative_of_compact_local_smooth_source
      hn hO (divergenceCoefficients g e)
      (fun y => -g.pullbackVolumeDensity e y * V (e y))
      (fun y => g.pullbackVolumeDensity e y * F (e y))
      (fun y => toL2 D univ w (e y)) (fun i y => p i y)
    · intro i j
      exact (contDiffOn_divergenceCoefficients e he hei i j).mono hOs
    · intro y hy
      apply Matrix.PosDef.of_dotProduct_mulVec_pos
      · ext i j
        change divergenceCoefficients g e y j i = divergenceCoefficients g e y i j
        exact divergenceCoefficients_symm e he hei (hOs hy) j i
      · intro v hv
        have hv' : (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
          intro hz
          apply hv
          exact congrArg WithLp.ofLp hz
        have hpos := divergenceCoefficients_pos (g := g) e he hei (hOs hy)
          (WithLp.toLp 2 v) hv'
        simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
          Finset.mul_sum, PiLp.toLp_apply, mul_left_comm, mul_comm, mul_assoc] using hpos
    · exact hρ.neg.mul ((hV.comp_contMDiffOn he).contDiffOn.mono hOs)
    · exact hρ.mul ((hF.comp_contMDiffOn he).contDiffOn.mono hOs)
    · intro K' _ hKO
      exact huL2.mono_measure (Measure.restrict_mono hKO le_rfl)
    · intro i K' _ hKO
      exact (Lp.memLp (p i)).mono_measure (Measure.restrict_mono hKO le_rfl)
    · intro i φ hφ hc hs
      exact localCoordinateDerivative_weak e he hei hK hKs hOK hO w i hφ hc hs
    · intro φ hφ hc hs
      exact weakSmoothForced_divergence_local V F hV hF w hweak
        e he hei hK hKs hOK hOΩ hφ hc hs
  obtain ⟨H, hHs, hHae⟩ := g.exists_smooth_representative_on_coordinate_image
    e he hei hO hOs (toL2 D univ w) hUs hUae
  exact ⟨e '' O, e.isOpen_image_of_subset_source hO hOs, hxO, hOΩ, H, hHs, hHae⟩

#print axioms exists_smooth_representative_of_native_smooth_forced

/-- On the actual closed manifold, a smooth representative satisfies the
actual forced pointwise equation. The test is its genuine smooth residual. -/
theorem native_schrodinger_eq_source_of_closed_smooth_transposed
    (D : LeviCivitaData g) {V F U : M → ℝ}
    (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V)
    (hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F)
    (hU : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ U)
    (hweak : ∀ f : EnergyTest D univ,
      (∫ y, (-D.laplacian f y + V y * f y) * U y ∂g.volumeMeasure) =
        ∫ y, f y * F y ∂g.volumeMeasure) :
    ∀ x, -D.laplacian U x + V x * U x = F x := by
  let R : M → ℝ := fun y => -D.laplacian U y + V y * U y - F y
  have hRs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ R :=
    ((D.contMDiff_laplacian hU).neg.add (hV.mul hU)).sub hF
  have hRc : HasCompactSupport R := (isClosed_tsupport R).isCompact
  have hUc : HasCompactSupport U := (isClosed_tsupport U).isCompact
  let f : EnergyTest D univ := ⟨R, hRs, hRc, subset_univ _⟩
  have hiL : Integrable (fun y => f y * (-D.laplacian U y + V y * U y))
      g.volumeMeasure :=
    (f.smooth.continuous.mul
      ((D.contMDiff_laplacian hU).neg.add (hV.mul hU)).continuous).integrable_of_hasCompactSupport
        f.hasCompactSupport.mul_right
  have hiF : Integrable (fun y => f y * F y) g.volumeMeasure :=
    (f.smooth.continuous.mul hF.continuous).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
  have hzero : (∫ y, R y * R y ∂g.volumeMeasure) = 0 := by
    calc
      _ = (∫ y, f y * (-D.laplacian U y + V y * U y) ∂g.volumeMeasure) -
          ∫ y, f y * F y ∂g.volumeMeasure := by
        rw [← integral_sub hiL hiF]
        congr 1
        funext y
        change R y * R y = R y * (-D.laplacian U y + V y * U y) - R y * F y
        dsimp only [R]
        ring
      _ = 0 := by
        rw [← native_schrodinger_integral_comm D hV f.smooth hU f.hasCompactSupport hUc,
          hweak f, sub_self]
  intro x
  have hx : R x = 0 := by
    by_contra hx
    let : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
    have hpos := integral_pos_of_integrable_nonneg_nonzero (μ := g.volumeMeasure)
      (hRs.continuous.mul hRs.continuous)
      ((hRs.continuous.mul hRs.continuous).integrable_of_hasCompactSupport hRc.mul_right)
      (fun y => mul_self_nonneg (R y)) (x := x) (mul_ne_zero hx hx)
    exact hpos.ne' hzero
  exact sub_eq_zero.mp hx

#print axioms native_schrodinger_eq_source_of_closed_smooth_transposed

end Yamabe3.Analysis
