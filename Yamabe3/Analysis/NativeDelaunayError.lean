import Yamabe3.Analysis.NativeDelaunayOperator
import Yamabe3.Analysis.Green.EuclideanResidual

/-!
# A uniform native-background error bound for all periodic end parameters

The background radius and constant are chosen from the actual density and
scalar curvature before the periodic profile, phase or neck is chosen. The
normal density first jet gives the missing radial factor. This is a genuine
estimate of the original metric's nonlinear scalar-six residual.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis.Delaunay

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet
open Yamabe3.Analysis.GreenParametrix

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem radialProfile_abs_deriv_le {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (_hpos : ∀ t, 0 < v t) (hd : ∀ t, |deriv v t| ≤ v t / 2)
    (τ : ℝ) {r : ℝ} (hr : 0 < r) :
    |deriv (radialProfile v τ) r| ≤ radialProfile v τ r / r := by
  have hl := (abs_le.mp (hd (τ - Real.log r))).1
  have hu := (abs_le.mp (hd (τ - Real.log r))).2
  have hs : 0 ≤ v (τ - Real.log r) / 2 + deriv v (τ - Real.log r) := by linarith
  have hb : v (τ - Real.log r) / 2 + deriv v (τ - Real.log r) ≤
      v (τ - Real.log r) := by linarith
  rw [radialProfile_deriv hv τ hr, abs_mul, abs_neg,
    abs_of_pos (div_pos (radialScale_pos r) hr), abs_of_nonneg hs]
  calc
    _ ≤ (radialScale r / r) * v (τ - Real.log r) :=
      mul_le_mul_of_nonneg_left hb (div_pos (radialScale_pos r) hr).le
    _ = radialProfile v τ r / r := by unfold radialProfile; ring

theorem native_delaunay_error_bound_of_density_bounds
    (g : RiemannianMetric 3 E3)
    (hGauss : ∀ x w : E3, g.inner x x w = inner ℝ x w)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hODE : ∀ t, deriv (deriv v) t = v t / 4 - 3 * v t ^ 5 / 4)
    (hpos : ∀ t, 0 < v t) (hd : ∀ t, |deriv v t| ≤ v t / 2)
    {c B K : ℝ} (hc : 0 < c) (hB : 0 ≤ B) (hK : 0 ≤ K)
    {x : E3} (hx : x ≠ 0)
    (hρ : c ≤ g.pullbackVolumeDensity id x)
    (hD : ‖fderiv ℝ (g.pullbackVolumeDensity id) x‖ ≤ B * ‖x‖)
    (hR : |g.leviCivitaData.scalarCurvature x| ≤ K) (τ : ℝ) :
    |-8 * g.leviCivitaData.laplacian (fun y : E3 => radialProfile v τ ‖y‖) x +
      g.leviCivitaData.scalarCurvature x * radialProfile v τ ‖x‖ -
      6 * radialProfile v τ ‖x‖ ^ 5| ≤
      (8 * B / c + K) * radialProfile v τ ‖x‖ := by
  let ρ := g.pullbackVolumeDensity id
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hρpos : 0 < ρ x := hc.trans_le hρ
  have hnum : |fderiv ℝ ρ x x| ≤ B * ‖x‖ ^ 2 := by
    calc
      _ = ‖fderiv ℝ ρ x x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ ρ x‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (B * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right hD hr.le
      _ = B * ‖x‖ ^ 2 := by ring
  have hcoef : |fderiv ℝ ρ x x / (ρ x * ‖x‖)| ≤ (B / c) * ‖x‖ := by
    calc
      _ = |fderiv ℝ ρ x x| / (ρ x * ‖x‖) := by
        rw [abs_div, abs_of_pos (mul_pos hρpos hr)]
      _ ≤ (B * ‖x‖ ^ 2) / (c * ‖x‖) := by gcongr
      _ = (B / c) * ‖x‖ := by field_simp
  have hFpos : 0 < radialProfile v τ ‖x‖ :=
    mul_pos (radialScale_pos _) (hpos _)
  have hFd := radialProfile_abs_deriv_le hv hpos hd τ hr
  rw [native_delaunay_operator_gauss g hGauss hv hODE τ hx]
  calc
    _ ≤ |-8 * (fderiv ℝ ρ x x / (ρ x * ‖x‖)) * deriv (radialProfile v τ) ‖x‖| +
        |g.leviCivitaData.scalarCurvature x * radialProfile v τ ‖x‖| := abs_add_le _ _
    _ = 8 * |fderiv ℝ ρ x x / (ρ x * ‖x‖)| * |deriv (radialProfile v τ) ‖x‖| +
        |g.leviCivitaData.scalarCurvature x| * radialProfile v τ ‖x‖ := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos hFpos]
      norm_num
    _ ≤ 8 * ((B / c) * ‖x‖) * (radialProfile v τ ‖x‖ / ‖x‖) +
        K * radialProfile v τ ‖x‖ := by gcongr
    _ = (8 * B / c + K) * radialProfile v τ ‖x‖ := by field_simp

/-- Radius and residual constant are selected before all profile and phase
parameters. Positivity and the native first density jet are the only local
geometric inputs, and the actual normal-chart theorem provides them. -/
theorem exists_uniform_native_delaunay_error_bound
    (g : RiemannianMetric 3 E3)
    (hGauss : ∀ x w : E3, g.inner x x w = inner ℝ x w)
    (hzero : fderiv ℝ (g.pullbackVolumeDensity id) 0 = 0) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
      ∀ (v : ℝ → ℝ), ContDiff ℝ ∞ v →
        (∀ t, deriv (deriv v) t = v t / 4 - 3 * v t ^ 5 / 4) →
        (∀ t, 0 < v t) → (∀ t, |deriv v t| ≤ v t / 2) →
        ∀ (τ : ℝ) (x : E3), 0 < ‖x‖ → ‖x‖ < r →
          |-8 * g.leviCivitaData.laplacian (fun y : E3 => radialProfile v τ ‖y‖) x +
            g.leviCivitaData.scalarCurvature x * radialProfile v τ ‖x‖ -
            6 * radialProfile v τ ‖x‖ ^ 5| ≤ C * radialProfile v τ ‖x‖ := by
  let ρ := g.pullbackVolumeDensity id
  let V := g.leviCivitaData.scalarCurvature
  obtain ⟨hρ, hρpos⟩ := native_density_smooth_positive g
  have hD : ContDiff ℝ ∞ (fderiv ℝ ρ) := hρ.fderiv_right (by simp)
  have hDD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ρ)) := hD.fderiv_right (by simp)
  have hV : Continuous V := g.leviCivitaData.contMDiff_scalarCurvature.continuous
  let c := ρ 0 / 2
  let B := ‖fderiv ℝ (fderiv ℝ ρ) 0‖ + 1
  let K := |V 0| + 1
  have hc : 0 < c := half_pos (hρpos 0)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hlow : ∀ᶠ x in 𝓝 (0 : E3), c < ρ x :=
    hρ.continuous.continuousAt.eventually
      (Ioi_mem_nhds (show c < ρ 0 by dsimp only [c]; linarith [hρpos 0]))
  have hcDD : Continuous (fun x : E3 => ‖fderiv ℝ (fderiv ℝ ρ) x‖) :=
    Continuous.norm (f := fderiv ℝ (fderiv ℝ ρ)) hDD.continuous
  have hdb : ∀ᶠ x in 𝓝 (0 : E3), ‖fderiv ℝ (fderiv ℝ ρ) x‖ < B :=
    hcDD.continuousAt.eventually
      (Iio_mem_nhds (show ‖fderiv ℝ (fderiv ℝ ρ) 0‖ < B by dsimp only [B]; linarith))
  have hvb : ∀ᶠ x in 𝓝 (0 : E3), |V x| < K :=
    hV.abs.continuousAt.eventually
      (Iio_mem_nhds (show |V 0| < K by dsimp only [K]; linarith))
  have hall : ∀ᶠ x in 𝓝 (0 : E3), c < ρ x ∧
      ‖fderiv ℝ (fderiv ℝ ρ) x‖ < B ∧ |V x| < K := by
    filter_upwards [hlow, hdb, hvb] with x hx1 hx2 hx3
    exact ⟨hx1, hx2, hx3⟩
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨r, 8 * B / c + K, hr, by positivity, ?_⟩
  intro v hv hODE hpos hd τ x hx hxr
  have hxb : x ∈ ball (0 : E3) r := by simpa using hxr
  have hjet := norm_fderiv_le_mul_norm hr hzero
    (fun y _ => hD.differentiable (by simp) y)
    (fun y hy => (hb hy).2.1.le) hxb
  exact native_delaunay_error_bound_of_density_bounds g hGauss hv hODE hpos hd
    hc hB hK (norm_pos_iff.mp hx) (hb hxb).1.le hjet (hb hxb).2.2.le τ

#print axioms radialProfile_abs_deriv_le
#print axioms native_delaunay_error_bound_of_density_bounds
#print axioms exists_uniform_native_delaunay_error_bound

end Yamabe3.Analysis.Delaunay
