import Yamabe3.Analysis.Green.NativePointSource
import Yamabe3.Analysis.Green.NativeResidualSupport
import Yamabe3.Analysis.Green.NativeNormalDensity
import Yamabe3.Analysis.Green.NativeChartOperatorTransfer
import Yamabe3.Analysis.Green.NativeChartTestExtension
import Yamabe3.Analysis.Green.NativeChartIntegralTransfer

/-!
# The actual point-source parametrix on an arbitrary smooth three-manifold

The final existence statement constructs its chart, cutoff, and residual
from the actual metric and pole. Its testing equation uses the native
Laplacian, scalar curvature and volume. No Dirac functional is passed to
the H1 inverse. The actual residual is proved to be in L2 before correction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet
open Yamabe3.Parametrix
open Yamabe3.Analysis.NormalCoordinates
open Yamabe3.Analysis.ChartOperatorTransfer

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- Transfer the proved native point source through an actual smooth chart
on the ball where the two actual metrics agree. -/
theorem native_chart_parametrix_test (g : RiemannianMetric 3 M)
    (gE : RiemannianMetric 3 E) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r : ℝ} (hr : 0 < r) (hrs : closedBall (0 : E) r ⊆ e.source)
    (hcoeff : ∀ x ∈ closedBall (0 : E) r,
      gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    (hGauss : ∀ x v : E, gE.inner x x v = inner ℝ x v)
    (hρ0 : gE.pullbackVolumeDensity id 0 = 1)
    (hzero : fderiv ℝ (gE.pullbackVolumeDensity id) 0 = 0)
    (χ : ContDiffBump (0 : E)) (hχr : χ.rOut < r)
    (φ : EnergyTest g.leviCivitaData univ) :
    (∫ y, (-g.leviCivitaData.laplacian φ y +
      (g.leviCivitaData.scalarCurvature y / 8) * φ y) * singular e χ y
        ∂g.volumeMeasure) =
      4 * Real.pi * φ (e 0) + ∫ y, φ y *
        coordinateExtension e (nativeResidual gE χ) y ∂g.volumeMeasure := by
  have hχball : tsupport χ ⊆ ball (0 : E) r := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball hχr
  have hχsource : tsupport χ ⊆ e.source :=
    hχball.trans (ball_subset_closedBall.trans hrs)
  have hdensity (x : E) (hx : x ∈ tsupport χ) :
      gE.pullbackVolumeDensity id x = g.pullbackVolumeDensity e x :=
    density_eq_of_coefficients_eq g gE e x (hcoeff x (ball_subset_closedBall (hχball hx)))
  obtain ⟨ψ, _, hψgerm, hψ0⟩ :=
    exists_coordinateEnergyTest gE e he hei hr hrs χ hχr φ.smooth
  have hP (x : E) (hx : x ∈ tsupport χ) :
      -gE.leviCivitaData.laplacian ψ x +
          (gE.leviCivitaData.scalarCurvature x / 8) * ψ x =
        -g.leviCivitaData.laplacian φ (e x) +
          (g.leviCivitaData.scalarCurvature (e x) / 8) * φ (e x) :=
    conformalP_eq_of_chart_coefficients_and_germ g gE g.leviCivitaData
      gE.leviCivitaData e he hei isOpen_ball (ball_subset_closedBall.trans hrs)
      (fun y hy => hcoeff y (ball_subset_closedBall hy)) (hχball hx)
      (φ.smooth.contMDiffAt) (hψgerm x hx).symm
  have hQ : Continuous (fun y => -g.leviCivitaData.laplacian φ y +
      (g.leviCivitaData.scalarCurvature y / 8) * φ y) :=
    (g.leviCivitaData.continuous_laplacian φ.smooth).neg.add
      ((g.leviCivitaData.continuous_scalarCurvature.div_const 8).mul φ.smooth.continuous)
  have hsm : Measurable (cutoffSingular χ) :=
    χ.continuous.measurable.mul measurable_norm.inv
  have hss : tsupport (cutoffSingular χ) ⊆ tsupport χ :=
    tsupport_cutoffSingular_subset χ
  have hFs : tsupport (nativeResidual gE χ) ⊆ tsupport χ :=
    tsupport_nativeResidual_subset gE χ
  calc
    _ = ∫ x, (-g.leviCivitaData.laplacian φ (e x) +
          (g.leviCivitaData.scalarCurvature (e x) / 8) * φ (e x)) *
        cutoffSingular χ x ∂gE.volumeMeasure :=
      integral_mul_coordinateExtension_eq_native g gE e he hei hsm
        (hss.trans hχsource) (fun x hx => hdensity x (hss hx)) hQ
    _ = ∫ x, (-gE.leviCivitaData.laplacian ψ x +
          (gE.leviCivitaData.scalarCurvature x / 8) * ψ x) *
        (χ x * ‖x‖⁻¹) ∂gE.volumeMeasure := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only [cutoffSingular]
      by_cases hx : x ∈ tsupport χ
      · rw [hP x hx]
      · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, mul_zero]
    _ = 4 * Real.pi * ψ 0 + ∫ x, ψ x * nativeResidual gE χ x ∂gE.volumeMeasure :=
      native_cutoff_pointSource_test gE hGauss hρ0 hzero χ ψ
    _ = 4 * Real.pi * φ (e 0) +
        ∫ x, φ (e x) * nativeResidual gE χ x ∂gE.volumeMeasure := by
      rw [hψ0]
      congr 1
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only
      by_cases hx : x ∈ tsupport (nativeResidual gE χ)
      · rw [(hψgerm x (hFs hx)).self_of_nhds]
        rfl
      · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    _ = _ := congrArg (fun t : ℝ => 4 * Real.pi * φ (e 0) + t)
      (integral_mul_coordinateExtension_eq_native g gE e he hei
        (measurable_nativeResidual gE χ) (hFs.trans hχsource)
        (fun x hx => hdensity x (hFs hx)) φ.smooth.continuous).symm

/-- Every actual smooth three-dimensional Riemannian metric and every pole
admit an actual cutoff Newton parametrix with an actual L2 residual.
All coordinate normalization and coefficient identities are constructed
inside the proof. The conclusion is the native distributional identity. -/
theorem exists_native_pointSource_parametrix (g : RiemannianMetric 3 M) (p : M) :
    ∃ (e : OpenPartialHomeomorph E M) (χ : ContDiffBump (0 : E)) (F : M → ℝ),
      e 0 = p ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      tsupport χ ⊆ e.source ∧
      MemLp (singular e χ) 2 g.volumeMeasure ∧ MemLp F 2 g.volumeMeasure ∧
      ∀ φ : EnergyTest g.leviCivitaData univ,
        (∫ y, (-g.leviCivitaData.laplacian φ y +
          (g.leviCivitaData.scalarCurvature y / 8) * φ y) * singular e χ y
            ∂g.volumeMeasure) =
          4 * Real.pi * φ p + ∫ y, φ y * F y ∂g.volumeMeasure := by
  obtain ⟨e, r, gE, _, hr, hrs, hep, he, hei, hcoeff, hGauss,
      _, _, hρ0, hzero, hρeq, _, _⟩ := exists_native_normalized_density g p
  let χ : ContDiffBump (0 : E) :=
    { rIn := r / 4, rOut := r / 2,
      rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  have hχr : χ.rOut < r := by dsimp [χ]; linarith
  have hχclosed : tsupport χ ⊆ closedBall (0 : E) r := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_closedBall hχr.le
  have hχsource : tsupport χ ⊆ e.source := hχclosed.trans hrs
  let F := coordinateExtension e (nativeResidual gE χ)
  have hFL2 : MemLp F 2 g.volumeMeasure :=
    memLp_coordinateExtension_of_native g gE e he hei (nativeResidual_memLp gE hzero χ)
      (fun x hx => hρeq x (hχclosed (tsupport_nativeResidual_subset gE χ hx)))
  refine ⟨e, χ, F, hep, he, hei, hχsource, memLp_singular g e he hei χ hχsource,
    hFL2, ?_⟩
  intro φ
  simpa only [hep] using
    native_chart_parametrix_test g gE e he hei hr hrs hcoeff hGauss hρ0 hzero χ hχr φ

#print axioms native_chart_parametrix_test
#print axioms exists_native_pointSource_parametrix

end Yamabe3.Analysis.GreenParametrix
