import Yamabe3.Analysis.NativeRadialLaplacian
import Yamabe3.Analysis.DelaunayRadialProfile
import Yamabe3.Analysis.Green.NativeChartOperatorTransfer
import Yamabe3.Analysis.Green.NativeNormalDensity
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateTest

/-!
# The actual Delaunay end profile in an arbitrary native background

The radial ODE is transported through an actual normal chart. The resulting
native scalar-six equation has the exact density and scalar-curvature error
of the original metric. The highest theorem constructs its chart and periodic
profile from the metric, point and admissible energy parameters; neither a
normal-coordinate condition nor a periodic ODE solution is a free input.

This is a local approximate-end construction. Its displayed nonzero error
must still be removed by the global nonlinear gluing argument.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis.Delaunay

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet
open Yamabe3.Parametrix Yamabe3.Analysis.GreenParametrix
open Yamabe3.Analysis.ChartOperatorTransfer Yamabe3.Analysis.NormalCoordinates

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem native_delaunay_operator_gauss (g : RiemannianMetric 3 E3)
    (hGauss : ∀ x w : E3, g.inner x x w = inner ℝ x w)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hODE : ∀ t, deriv (deriv v) t = v t / 4 - 3 * v t ^ 5 / 4)
    (τ : ℝ) {x : E3} (hx : x ≠ 0) :
    -8 * g.leviCivitaData.laplacian (fun y : E3 => radialProfile v τ ‖y‖) x +
      g.leviCivitaData.scalarCurvature x * radialProfile v τ ‖x‖ -
      6 * radialProfile v τ ‖x‖ ^ 5 =
      -8 * (fderiv ℝ (g.pullbackVolumeDensity id) x x /
        (g.pullbackVolumeDensity id x * ‖x‖)) * deriv (radialProfile v τ) ‖x‖ +
        g.leviCivitaData.scalarCurvature x * radialProfile v τ ‖x‖ := by
  rw [native_laplacian_radial g hGauss _ (radialProfile_contDiffOn hv τ) hx]
  have h := radialProfile_radial_equation hv hODE τ (norm_pos_iff.mpr hx)
  nlinarith only [h]

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]

theorem coordinate_radialProfile_smooth
    (e : OpenPartialHomeomorph E3 M)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (τ : ℝ)
    {x : E3} (hxs : x ∈ e.source) (hx : x ≠ 0) :
    ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (coordinateExtension e (fun y => radialProfile v τ ‖y‖)) (e x) := by
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hs : ContDiffAt ℝ ∞ (fun y : E3 => radialProfile v τ ‖y‖) x :=
    ((radialProfile_contDiffOn hv τ).contDiffAt (isOpen_Ioi.mem_nhds hp)).comp x
      (contDiffAt_norm ℝ hx)
  have hst : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun y : E3 => radialProfile v τ ‖y‖) (e.symm (e x)) := by
    rw [e.left_inv hxs]
    exact hs.contMDiffAt
  apply ContMDiffAt.congr_of_eventuallyEq _
    (coordinateExtension_eventuallyEq e _ (e.map_source hxs))
  exact hst.comp (e x) (hei.contMDiffAt (e.open_target.mem_nhds (e.map_source hxs)))

theorem native_delaunay_operator_in_chart
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E3)
    (e : OpenPartialHomeomorph E3 M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r : ℝ} (hrs : closedBall (0 : E3) r ⊆ e.source)
    (hcoeff : ∀ x ∈ closedBall (0 : E3) r,
      gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    (hGauss : ∀ x w : E3, gE.inner x x w = inner ℝ x w)
    (hρeq : ∀ x ∈ closedBall (0 : E3) r,
      gE.pullbackVolumeDensity id x = g.pullbackVolumeDensity e x)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hODE : ∀ t, deriv (deriv v) t = v t / 4 - 3 * v t ^ 5 / 4)
    (τ : ℝ) {x : E3} (hx : x ≠ 0) (hxr : ‖x‖ < r) :
    let u := coordinateExtension e (fun y => radialProfile v τ ‖y‖);
    -8 * g.leviCivitaData.laplacian u (e x) +
      g.leviCivitaData.scalarCurvature (e x) * u (e x) - 6 * u (e x) ^ 5 =
      -8 * (fderiv ℝ (g.pullbackVolumeDensity e) x x /
        (g.pullbackVolumeDensity e x * ‖x‖)) * deriv (radialProfile v τ) ‖x‖ +
        g.leviCivitaData.scalarCurvature (e x) * u (e x) := by
  dsimp only
  have hxb : x ∈ ball (0 : E3) r := by simpa using hxr
  have hxs : x ∈ e.source := hrs (ball_subset_closedBall hxb)
  have hs := coordinate_radialProfile_smooth e hei hv τ hxs hx
  have hcomp : (coordinateExtension e (fun y => radialProfile v τ ‖y‖) ∘ e) =ᶠ[𝓝 x]
      (fun y : E3 => radialProfile v τ ‖y‖) := by
    filter_upwards [e.open_source.mem_nhds hxs] with y hy
    exact coordinateExtension_comp_apply e _ hy
  have hL := laplacian_eq_of_chart_coefficients_and_germ g gE
    g.leviCivitaData gE.leviCivitaData e he hei isOpen_ball
    (fun y hy => hrs (ball_subset_closedBall hy))
    (fun y hy => hcoeff y (ball_subset_closedBall hy)) hxb hs hcomp
  have hR := scalarCurvature_eq_of_chart_coefficients g gE
    g.leviCivitaData gE.leviCivitaData e he isOpen_ball
    (fun y hy => hrs (ball_subset_closedBall hy))
    (fun y hy => hcoeff y (ball_subset_closedBall hy)) hxb
  have hρgerm : gE.pullbackVolumeDensity id =ᶠ[𝓝 x] g.pullbackVolumeDensity e := by
    filter_upwards [isOpen_ball.mem_nhds hxb] with y hy
    exact hρeq y (ball_subset_closedBall hy)
  rw [coordinateExtension_comp_apply e _ hxs, ← hL, ← hR]
  have h := native_delaunay_operator_gauss gE hGauss hv hODE τ hx
  rw [hρgerm.self_of_nhds, hρgerm.fderiv_eq] at h
  exact h

/-- A genuine local periodic end at any specified point of any smooth native
three-dimensional metric, retaining its exact original-background error. -/
theorem exists_native_delaunay_local_model
    (g : RiemannianMetric 3 M) (p : M) {ε energy : ℝ}
    (hε : 0 < ε) (henergy : 0 < energy) (hsmall : ε ^ 2 * energy < 3 / 8) :
    ∃ (e : OpenPartialHomeomorph E3 M) (r η : ℝ) (v : ℝ → ℝ) (T : ℝ),
      0 < r ∧ closedBall (0 : E3) r ⊆ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      g.pullbackVolumeDensity e 0 = 1 ∧ fderiv ℝ (g.pullbackVolumeDensity e) 0 = 0 ∧
      0 < η ∧ η ^ 2 * (1 - η ^ 4) = ε ^ 2 * energy ∧
      ε * Real.sqrt energy ≤ η ∧ η ≤ 2 * ε * Real.sqrt energy ∧
      0 < T ∧ ContDiff ℝ ∞ v ∧ Function.Periodic v T ∧
      (∀ t, η ≤ v t ∧ v t < 1) ∧ (∀ t, |deriv v t| < v t / 2) ∧
      ∀ (τ : ℝ) (x : E3), 0 < ‖x‖ → ‖x‖ < r →
        let u := coordinateExtension e (fun y => radialProfile v τ ‖y‖)
        ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ u (e x) ∧
        0 < u (e x) ∧ η ^ 2 * ‖x‖⁻¹ ≤ u (e x) ^ 2 ∧
        -8 * g.leviCivitaData.laplacian u (e x) +
          g.leviCivitaData.scalarCurvature (e x) * u (e x) - 6 * u (e x) ^ 5 =
          -8 * (fderiv ℝ (g.pullbackVolumeDensity e) x x /
            (g.pullbackVolumeDensity e x * ‖x‖)) * deriv (radialProfile v τ) ‖x‖ +
            g.leviCivitaData.scalarCurvature (e x) * u (e x) := by
  obtain ⟨e, r, gE, D, hr, hrs, hep, he, hei, hcoeff, hGauss,
    _, _, _, _, hρeq, hρ0, hDρ0⟩ := exists_native_normalized_density g p
  obtain ⟨η, v, T, hη, hηenergy, hηlower, hηupper, hT, hv, hperiod,
    hbounds, _, _, _, hODE, _, hderiv, _⟩ :=
    exists_delaunay_energy_parameters hε henergy hsmall
  refine ⟨e, r, η, v, T, hr, hrs, hep, he, hei, hρ0, hDρ0, hη,
    hηenergy, hηlower, hηupper, hT, hv, hperiod, hbounds, hderiv, ?_⟩
  intro τ x hx hxr
  have hx0 : x ≠ 0 := norm_pos_iff.mp hx
  have hxs : x ∈ e.source := hrs (ball_subset_closedBall (by simpa using hxr))
  have hpos := radialProfile_cylindrical_lower_bound hη (fun t => (hbounds t).1) τ hx
  refine ⟨coordinate_radialProfile_smooth e hei hv τ hxs hx0, ?_, ?_, ?_⟩
  · simpa only [coordinateExtension_comp_apply e _ hxs] using hpos.1
  · simpa only [coordinateExtension_comp_apply e _ hxs] using hpos.2
  · exact native_delaunay_operator_in_chart g gE e he hei hrs hcoeff hGauss hρeq
      hv hODE τ hx0 hxr

#print axioms native_delaunay_operator_gauss
#print axioms coordinate_radialProfile_smooth
#print axioms native_delaunay_operator_in_chart
#print axioms exists_native_delaunay_local_model

end Yamabe3.Analysis.Delaunay
