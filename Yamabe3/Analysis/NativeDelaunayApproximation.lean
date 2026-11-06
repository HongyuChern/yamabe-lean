import Yamabe3.Analysis.NativeDelaunayError

/-!
# Actual end models with geometry fixed before all neck parameters

The metric and prescribed point alone choose the genuine normal chart,
positive radius and residual constant. Every admissible energy pair then
supplies a true periodic profile, for every phase, with the native scalar-six
residual bounded by C times that same positive profile. The constant has no
neck or phase dependence. This local error estimate does not remove the error.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis.Delaunay

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet
open Yamabe3.Analysis.NormalCoordinates Yamabe3.Analysis.ChartOperatorTransfer

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]

theorem exists_uniform_native_delaunay_models
    (g : RiemannianMetric 3 M) (p : M) :
    ∃ (e : OpenPartialHomeomorph E3 M) (r C : ℝ),
      0 < r ∧ closedBall (0 : E3) r ⊆ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      g.pullbackVolumeDensity e 0 = 1 ∧ fderiv ℝ (g.pullbackVolumeDensity e) 0 = 0 ∧
      (∀ x ∈ ball (0 : E3) r, ∀ w : E3,
        g.pullbackCoefficients e x x w = inner ℝ x w) ∧
      0 ≤ C ∧ ∀ ε energy : ℝ, 0 < ε → 0 < energy → ε ^ 2 * energy < 3 / 8 →
        ∃ (η : ℝ) (v : ℝ → ℝ) (T : ℝ),
          0 < η ∧ η ^ 2 * (1 - η ^ 4) = ε ^ 2 * energy ∧
          ε * Real.sqrt energy ≤ η ∧ η ≤ 2 * ε * Real.sqrt energy ∧
          0 < T ∧ ContDiff ℝ ∞ v ∧ Function.Periodic v T ∧
          (∀ t, η ≤ v t ∧ v t < 1) ∧
          ∀ (τ : ℝ) (x : E3), 0 < ‖x‖ → ‖x‖ < r →
            let u := coordinateExtension e (fun y => radialProfile v τ ‖y‖)
            ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ u (e x) ∧
            0 < u (e x) ∧ η ^ 2 * ‖x‖⁻¹ ≤ u (e x) ^ 2 ∧
            (-8 * g.leviCivitaData.laplacian u (e x) +
              g.leviCivitaData.scalarCurvature (e x) * u (e x) - 6 * u (e x) ^ 5 =
              -8 * (fderiv ℝ (g.pullbackVolumeDensity e) x x /
                (g.pullbackVolumeDensity e x * ‖x‖)) * deriv (radialProfile v τ) ‖x‖ +
                g.leviCivitaData.scalarCurvature (e x) * u (e x)) ∧
            |-8 * g.leviCivitaData.laplacian u (e x) +
              g.leviCivitaData.scalarCurvature (e x) * u (e x) - 6 * u (e x) ^ 5| ≤
              C * u (e x) := by
  obtain ⟨e, R, gE, D, hR, hRs, hep, he, hei, hcoeff, hGauss,
    _, _, _, hzero, hρeq, hρ0, hDρ0⟩ := exists_native_normalized_density g p
  obtain ⟨r0, C, hr0, hC, hb⟩ := exists_uniform_native_delaunay_error_bound gE hGauss hzero
  let r := min R r0
  have hr : 0 < r := lt_min hR hr0
  have hrs : closedBall (0 : E3) r ⊆ e.source :=
    (closedBall_subset_closedBall (min_le_left _ _)).trans hRs
  have hnativeGauss : ∀ x ∈ ball (0 : E3) r, ∀ w : E3,
      g.pullbackCoefficients e x x w = inner ℝ x w := by
    intro x hx w
    rw [← hcoeff x ((closedBall_subset_closedBall (min_le_left _ _))
      (ball_subset_closedBall hx))]
    exact hGauss x w
  refine ⟨e, r, C, hr, hrs, hep, he, hei, hρ0, hDρ0, hnativeGauss, hC, ?_⟩
  intro ε energy hε henergy hsmall
  obtain ⟨η, v, T, hη, hηenergy, hηlower, hηupper, hT, hv, hperiod,
    hbounds, _, _, _, hODE, _, hderiv, _⟩ :=
    exists_delaunay_energy_parameters hε henergy hsmall
  refine ⟨η, v, T, hη, hηenergy, hηlower, hηupper, hT, hv, hperiod, hbounds, ?_⟩
  intro τ x hx hxr
  have hx0 : x ≠ 0 := norm_pos_iff.mp hx
  have hxR : ‖x‖ < R := hxr.trans_le (min_le_left _ _)
  have hxr0 : ‖x‖ < r0 := hxr.trans_le (min_le_right _ _)
  have hxb : x ∈ ball (0 : E3) R := by simpa using hxR
  have hxs : x ∈ e.source := hRs (ball_subset_closedBall hxb)
  have hs := coordinate_radialProfile_smooth e hei hv τ hxs hx0
  have hpos := radialProfile_cylindrical_lower_bound hη (fun t => (hbounds t).1) τ hx
  refine ⟨hs, ?_, ?_, ?_, ?_⟩
  · simpa only [coordinateExtension_comp_apply e _ hxs] using hpos.1
  · simpa only [coordinateExtension_comp_apply e _ hxs] using hpos.2
  · exact native_delaunay_operator_in_chart g gE e he hei hRs hcoeff hGauss hρeq
      hv hODE τ hx0 hxR
  · have hcomp : (coordinateExtension e (fun y => radialProfile v τ ‖y‖) ∘ e) =ᶠ[𝓝 x]
        (fun y : E3 => radialProfile v τ ‖y‖) := by
      filter_upwards [e.open_source.mem_nhds hxs] with y hy
      exact coordinateExtension_comp_apply e _ hy
    have hL := laplacian_eq_of_chart_coefficients_and_germ g gE
      g.leviCivitaData gE.leviCivitaData e he hei isOpen_ball
      (fun y hy => hRs (ball_subset_closedBall hy))
      (fun y hy => hcoeff y (ball_subset_closedBall hy)) hxb hs hcomp
    have hRnative := scalarCurvature_eq_of_chart_coefficients g gE
      g.leviCivitaData gE.leviCivitaData e he isOpen_ball
      (fun y hy => hRs (ball_subset_closedBall hy))
      (fun y hy => hcoeff y (ball_subset_closedBall hy)) hxb
    rw [coordinateExtension_comp_apply e _ hxs, ← hL, ← hRnative]
    exact hb v hv hODE (fun t => hη.trans_le (hbounds t).1)
      (fun t => (hderiv t).le) τ x hx hxr0

#print axioms exists_uniform_native_delaunay_models

end Yamabe3.Analysis.Delaunay
