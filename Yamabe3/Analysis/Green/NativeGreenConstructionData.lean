import Yamabe3.Analysis.Green.NativeGreenPositive
import Yamabe3.Analysis.Green.NativeNormalDensityWithMetricJet

/-!
# Retained actual construction data for Green symmetry and mass estimates

This is the same completed native construction, retaining the actual
coordinate metric, residual formula and continuous weak-inverse
representative. None of these are inputs to the existence theorem.
Keeping the same witnesses avoids silently changing normal coordinates
or choosing an unrelated Green representative in downstream arguments.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set MeasureTheory Metric
open scoped Manifold ContDiff

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet
open Yamabe3.Parametrix
open Yamabe3.Analysis.NormalCoordinates
open Yamabe3.Analysis.GreenPositivity

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

/-- All witnesses for the native normalized Green construction, with their
actual geometric and weak-solution identities. The only inputs are the
retained metric, true positive Yamabe constant and chosen pole. -/
theorem exists_native_green_construction_data (g : RiemannianMetric 3 M)
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
      ∀ x : M, x ≠ p → 0 < singular e χ x - U x := by
  obtain ⟨e, r, gE, _, hr, hrs, hep, he, hei, hB0, hΓ0, hcoeff, hGauss,
      _, _, hρ0, hzero, hρeq, _, _⟩ := exists_native_normalized_density_with_metricJet g p
  let χ : ContDiffBump (0 : E) :=
    { rIn := r / 4, rOut := r / 2,
      rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  have hχr : χ.rOut < r := by dsimp [χ]; linarith
  have hχclosed : tsupport χ ⊆ closedBall (0 : E) r := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_closedBall hχr.le
  have hχsource : tsupport χ ⊆ e.source := hχclosed.trans hrs
  let F := coordinateExtension e (nativeResidual gE χ)
  have hF : MemLp F 2 g.volumeMeasure :=
    memLp_coordinateExtension_of_native g gE e he hei (nativeResidual_memLp gE hzero χ)
      (fun x hx => hρeq x (hχclosed (tsupport_nativeResidual_subset gE χ hx)))
  have hΦ : MemLp (singular e χ) 2 g.volumeMeasure := memLp_singular g e he hei χ hχsource
  have hΦs : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (singular e χ) ({p}ᶜ) := by
    simpa only [hep] using contMDiffOn_singular e hei χ hχsource
  have hparam (φ : EnergyTest g.leviCivitaData univ) :
      (∫ y, (-g.leviCivitaData.laplacian φ y +
        (g.leviCivitaData.scalarCurvature y / 8) * φ y) * singular e χ y
          ∂g.volumeMeasure) =
        4 * Real.pi * φ p + ∫ y, φ y * F y ∂g.volumeMeasure := by
    simpa only [hep] using
      native_chart_parametrix_test g gE e he hei hr hrs hcoeff hGauss hρ0 hzero χ hχr φ
  obtain ⟨U, hUc, hUae, hGmem, hGs, hGP, hGt⟩ :=
    parametrix_correction_exists_smooth g hY p (singular e χ) F hΦ hF hΦs hparam
  have hnear : ∃ O : Set M, IsOpen O ∧ p ∈ O ∧
      ∀ x ∈ O, x ≠ p → 0 < singular e χ x - U x := by
    simpa only [hep] using
      singular_sub_continuous_pos_on_punctured_neighborhood e χ hχsource hUc.continuousAt
  have hnearnonneg : ∃ O : Set M, IsOpen O ∧ p ∈ O ∧
      ∀ x ∈ O, x ≠ p → 0 ≤ singular e χ x - U x := by
    obtain ⟨O, hO, hp, hs⟩ := hnear
    exact ⟨O, hO, hp, fun x hx hxp => (hs x hx hxp).le⟩
  have hGn := nonneg_of_native_pointSource g hY p (fun x => singular e χ x - U x)
    hGs hnearnonneg hGt
  have hpositive := pos_of_native_green_nonneg g p (fun x => singular e χ x - U x)
    hGs hGP hGn hnear
  exact ⟨e, r, gE, χ, F, hF, U, hr, hrs, hep, he, hei, hχr, hχsource,
    hB0, hΓ0, hcoeff, hGauss, hρ0, hzero, rfl, hUc, hUae, hGmem, hGs, hGP, hGt, hpositive⟩

#print axioms exists_native_green_construction_data

end Yamabe3.Analysis.GreenParametrix
