import Yamabe3.Analysis.UniformElliptic.NativeCorrectionC2
import Yamabe3.Analysis.Green.NativeCorrectionLocalEquation
import Yamabe3.Analysis.Green.NativeCorrectionHolder

/-!
# The constructed native Green correction has pointwise C2 decay

The same actual normal chart, extended native metric, cutoff, residual and
continuous H1 inverse representative are retained. The local correction PDE
and smoothness come from the completed native Green construction, and its
Holder estimate comes from genuine H2 regularity. No regular-part derivative
estimate, coordinate equation or uniform inverse constant is an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Metric MeasureTheory
open scoped Manifold ContDiff

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet Yamabe3.Parametrix
open Yamabe3.Analysis.GreenRegularPart Yamabe3.Analysis.UniformElliptic

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual same-witness construction data, strengthened by the true
pointwise first and second derivative bounds of its own correction. -/
theorem exists_native_green_construction_C2_data (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (p : M) :
    ∃ (e : OpenPartialHomeomorph E M) (r : ℝ) (gE : RiemannianMetric 3 E)
      (χ : ContDiffBump (0 : E)) (F : M → ℝ) (hF : MemLp F 2 g.volumeMeasure)
      (U : M → ℝ),
      0 < r ∧ closedBall (0 : E) r ⊆ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      χ.rOut < r ∧ tsupport χ ⊆ e.source ∧
      g.pullbackCoefficients e 0 = innerSL ℝ ∧
      CoordinateExponential.christoffelBilinear (g.pullbackCoefficients e) 0 = 0 ∧
      (∀ x ∈ closedBall (0 : E) r,
        gE.euclideanCoefficients x = g.pullbackCoefficients e x) ∧
      (∀ x v : E, gE.inner x x v = inner ℝ x v) ∧
      gE.pullbackVolumeDensity id 0 = 1 ∧
      fderiv ℝ (gE.pullbackVolumeDensity id) 0 = 0 ∧
      F = coordinateExtension e (nativeResidual gE χ) ∧ Continuous U ∧
      U =ᵐ[g.volumeMeasure]
        (toL2 g.leviCivitaData univ
          (closedConformalLaplacianL2Solution g hY (hF.toLp F)) : M → ℝ) ∧
      MemLp (fun x => singular e χ x - U x) 2 g.volumeMeasure ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x => singular e χ x - U x) ({p}ᶜ) ∧
      (∀ x ∈ ({p}ᶜ : Set M),
        -g.leviCivitaData.laplacian (fun y => singular e χ y - U y) x +
          (g.leviCivitaData.scalarCurvature x / 8) * (singular e χ x - U x) = 0) ∧
      (∀ φ : EnergyTest g.leviCivitaData univ,
        (∫ x, (-g.leviCivitaData.laplacian φ x +
          (g.leviCivitaData.scalarCurvature x / 8) * φ x) * (singular e χ x - U x)
            ∂g.volumeMeasure) = 4 * Real.pi * φ p) ∧
      (∀ x : M, x ≠ p → 0 < singular e χ x - U x) ∧
      ∃ δ C : ℝ, 0 < δ ∧ δ ≤ r ∧ δ ≤ χ.rIn ∧ 0 ≤ C ∧
        ∀ x : E, 0 < ‖x‖ → ‖x‖ < δ →
          ‖U (e x) - U p‖ ≤ C * ‖x‖ ^ (1 / 2 : ℝ) ∧
          ‖x‖ * ‖fderiv ℝ (fun y => U (e y)) x‖ ≤ C * ‖x‖ ^ (1 / 2 : ℝ) ∧
          ‖x‖ ^ 2 * ‖fderiv ℝ (fderiv ℝ (fun y => U (e y))) x‖ ≤
            C * ‖x‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨e, r, gE, χ, F, hF, U, hr, hrs, hep, he, hei, hχr, hχs,
    hB0, hΓ0, hcoeff, hGauss, hρ0, hzero, hFformula, hUc, hUae,
    hGmem, hGs, hGP, hGt, hGpos⟩ := exists_native_green_construction_data g hY p
  have he0 : (0 : E) ∈ e.source := hrs (mem_closedBall_self hr.le)
  have hgE0 : gE.euclideanCoefficients 0 = innerSL ℝ :=
    (hcoeff 0 (mem_closedBall_self hr.le)).trans hB0
  obtain ⟨hUs, hUP⟩ := native_correction_smooth_and_equation_in_chart
    g gE e he hei r hr hrs hcoeff hGauss χ hχs U
    (by simpa only [hep] using hGs) (by simpa only [hep] using hGP)
  obtain ⟨ρ, hρ, _, H, hH, hholder⟩ :=
    closedL2Solution_holder_half_in_chart g hY (hF.toLp F) e he hei he0 U hUc hUae
  let R := min (min r χ.rIn) ρ
  have hR : 0 < R := lt_min (lt_min hr χ.rIn_pos) hρ
  have hRO : ball (0 : E) R \ {0} ⊆ ball (0 : E) (min r χ.rIn) \ {0} :=
    diff_subset_diff_left (ball_subset_ball (min_le_left _ _))
  have hvalue (x : E) (hx : x ∈ ball (0 : E) R \ {0}) :
      ‖U (e x) - U p‖ ≤ H * ‖x‖ ^ (1 / 2 : ℝ) := by
    have hnorm : ‖x‖ < ρ := by
      have hxR : ‖x‖ < R := by simpa using hx.1
      exact hxR.trans_le (min_le_right _ _)
    simpa only [hep] using hholder x hnorm
  obtain ⟨δ, C, hδ, hδR, hC, hjet⟩ := exists_native_correction_C2_bound
    gE hgE0 hρ0 hzero χ hR (hUs.mono hRO) (fun x hx => hUP x (hRO hx))
    (U p) H hH hvalue
  refine ⟨e, r, gE, χ, F, hF, U, hr, hrs, hep, he, hei, hχr, hχs,
    hB0, hΓ0, hcoeff, hGauss, hρ0, hzero, hFformula, hUc, hUae,
    hGmem, hGs, hGP, hGt, hGpos, δ, C, hδ, ?_, ?_, hC, hjet⟩
  · exact hδR.trans ((min_le_left _ _).trans (min_le_left _ _))
  · exact hδR.trans ((min_le_left _ _).trans (min_le_right _ _))

#print axioms exists_native_green_construction_C2_data

end Yamabe3.Analysis.GreenParametrix
