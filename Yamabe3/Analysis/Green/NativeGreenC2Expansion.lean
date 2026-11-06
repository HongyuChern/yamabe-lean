import Yamabe3.Analysis.Green.NativeGreenCorrectionC2Data
import Yamabe3.Analysis.Green.RegularPartC2Transfer

/-!
# Actual normalized Green functions with pointwise C2 regular-part estimates

The derivatives below are the true Frechet derivatives of G composed with
the same constructed normal chart minus the Euclidean inverse radius. The
cutoff is identically one on a neighborhood of every evaluation point, so
all first and second jets equal those of the negative correction. No sphere
average or substitute regular-part definition is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Metric MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet Yamabe3.Parametrix

variable {M : Type*} [TopologicalSpace M]

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

/-- Every actual positive-Yamabe three-manifold has its normalized positive
Green function with a genuine pointwise C2 half-Holder regular-part remainder
in one actual normal Gauss chart. No derivative decay is a premise. -/
theorem exists_native_green_with_C2_expansion (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (p : M) :
    ∃ (e : OpenPartialHomeomorph E M) (G : M → ℝ) (a δ C : ℝ),
      e 0 = p ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      g.pullbackCoefficients e 0 = innerSL ℝ ∧
      CoordinateExponential.christoffelBilinear (g.pullbackCoefficients e) 0 = 0 ∧
      0 < δ ∧ closedBall (0 : E) δ ⊆ e.source ∧ 0 ≤ C ∧
      (∀ x ∈ ball (0 : E) δ, ∀ v : E,
        g.pullbackCoefficients e x x v = inner ℝ x v) ∧
      MemLp G 2 g.volumeMeasure ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ G ({p}ᶜ) ∧
      (∀ x ∈ ({p}ᶜ : Set M), -g.leviCivitaData.laplacian G x +
        (g.leviCivitaData.scalarCurvature x / 8) * G x = 0) ∧
      (∀ φ : EnergyTest g.leviCivitaData univ,
        (∫ x, (-g.leviCivitaData.laplacian φ x +
          (g.leviCivitaData.scalarCurvature x / 8) * φ x) * G x
            ∂g.volumeMeasure) = 4 * Real.pi * φ p) ∧
      (∀ x : M, x ≠ p → 0 < G x) ∧
      ∀ x : E, 0 < ‖x‖ → ‖x‖ < δ →
        ‖G (e x) - ‖x‖⁻¹ - a‖ ≤ C * ‖x‖ ^ (1 / 2 : ℝ) ∧
        ‖x‖ * ‖fderiv ℝ (fun y => G (e y) - ‖y‖⁻¹) x‖ ≤ C * ‖x‖ ^ (1 / 2 : ℝ) ∧
        ‖x‖ ^ 2 * ‖fderiv ℝ (fderiv ℝ (fun y => G (e y) - ‖y‖⁻¹)) x‖ ≤
          C * ‖x‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨e, r, gE, χ, F, hF, U, hr, hrs, hep, he, hei, _, hχs,
    hB0, hΓ0, hcoeff, hGauss, _, _, _, _, _, hGmem, hGs, hGP, hGt, hGpos,
    δ, C, hδ, hδr, hδχ, hC, hj⟩ := exists_native_green_construction_C2_data g hY p
  refine ⟨e, (fun y => singular e χ y - U y), -U p, δ, C,
    hep, he, hei, hB0, hΓ0, hδ, (closedBall_subset_closedBall hδr).trans hrs,
    hC, ?_, hGmem, hGs, hGP, hGt, hGpos, ?_⟩
  · intro x hx v
    have hxr : x ∈ closedBall (0 : E) r :=
      closedBall_subset_closedBall hδr (ball_subset_closedBall hx)
    rw [← hcoeff x hxr]
    exact hGauss x v
  · exact regularPart_C2_of_correction e χ hχs U hδχ (U p) C hj

#print axioms exists_native_green_with_C2_expansion

end Yamabe3.Analysis.GreenParametrix
