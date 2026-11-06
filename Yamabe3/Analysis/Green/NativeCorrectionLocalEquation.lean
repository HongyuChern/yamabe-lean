import Yamabe3.Analysis.Green.NativeNewtonPointwise
import Yamabe3.Analysis.Green.NativeScaledResidual
import Yamabe3.Analysis.Green.NativeGreenConstructionData
import Yamabe3.Analysis.Green.NativeChartOperatorTransfer
import PoincareLib.Geometry.Riemannian.ScalarOperators.Linearity

/-!
# The same constructed correction satisfies the true native local equation

The actual Green function is the already constructed cutoff singularity
minus its continuous weak-inverse correction. Its proved smoothness and
native homogeneous equation imply smoothness of that same correction away
from the pole. The actual Gauss metric computes the cutoff source, and the
genuine chart transport gives P U = nativeResidual in that same chart.

Local Laplacian subtraction is justified through actual smooth compact
extensions of germs; neither summand is assumed smooth across the pole.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric MeasureTheory
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet Yamabe3.Parametrix
open Yamabe3.Analysis.ChartOperatorTransfer

theorem native_laplacian_sub_on (g : RiemannianMetric 3 E)
    {Ω : Set E} (hΩ : IsOpen Ω) {f h : E → ℝ}
    (hf : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f Ω)
    (hh : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ h Ω)
    {x : E} (hx : x ∈ Ω) :
    g.leviCivitaData.laplacian (fun y => f y - h y) x =
      g.leviCivitaData.laplacian f x - g.leviCivitaData.laplacian h x := by
  obtain ⟨F, hF, _, _, hFf⟩ := exists_compact_smooth_germ hΩ hf hx
  obtain ⟨H, hH, _, _, hHh⟩ := exists_compact_smooth_germ hΩ hh hx
  calc
    _ = g.leviCivitaData.laplacian (fun y => F y - H y) x :=
      (g.leviCivitaData.laplacian_eq_of_eventuallyEq (hFf.sub hHh)).symm
    _ = g.leviCivitaData.laplacian F x - g.leviCivitaData.laplacian H x :=
      g.leviCivitaData.laplacian_sub hF hH x
    _ = _ := by
      rw [g.leviCivitaData.laplacian_eq_of_eventuallyEq hFf,
        g.leviCivitaData.laplacian_eq_of_eventuallyEq hHh]

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- All geometric and solution inputs here are retained by
`exists_native_green_construction_data`; no smooth correction or local
correction equation is supplied as an additional premise. -/
theorem native_correction_smooth_and_equation_in_chart
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (r : ℝ) (hr : 0 < r) (hrs : closedBall (0 : E) r ⊆ e.source)
    (hcoeff : ∀ x ∈ closedBall (0 : E) r,
      gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    (hGauss : ∀ x v : E, gE.inner x x v = inner ℝ x v)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source)
    (U : M → ℝ)
    (hGs : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y => singular e χ y - U y) ({e 0}ᶜ))
    (hGP : ∀ y ∈ ({e 0}ᶜ : Set M),
      -g.leviCivitaData.laplacian (fun z => singular e χ z - U z) y +
        (g.leviCivitaData.scalarCurvature y / 8) * (singular e χ y - U y) = 0) :
    ContDiffOn ℝ ∞ (fun x => U (e x))
      (ball (0 : E) (min r χ.rIn) \ {0}) ∧
    ∀ x ∈ ball (0 : E) (min r χ.rIn) \ {0},
      -gE.leviCivitaData.laplacian (fun y => U (e y)) x +
        (gE.leviCivitaData.scalarCurvature x / 8) * U (e x) = nativeResidual gE χ x := by
  let Ω : Set E := ball (0 : E) (min r χ.rIn) \ {0}
  have hΩ : IsOpen Ω := isOpen_ball.sdiff isClosed_singleton
  have h0 : (0 : E) ∈ e.source := hrs (mem_closedBall_self hr.le)
  have hxball {x : E} (hx : x ∈ Ω) : x ∈ ball (0 : E) r :=
    ball_subset_ball (min_le_left _ _) hx.1
  have hxinner {x : E} (hx : x ∈ Ω) : x ∈ ball (0 : E) χ.rIn :=
    ball_subset_ball (min_le_right _ _) hx.1
  have hxsource {x : E} (hx : x ∈ Ω) : x ∈ e.source :=
    hrs (ball_subset_closedBall (hxball hx))
  have haway {x : E} (hx : x ∈ Ω) : e x ≠ e 0 := by
    intro heq
    have hx0 : x = 0 := e.injOn (hxsource hx) h0 heq
    exact hx.2 (by simp [hx0])
  have hΦM : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (singular e χ) ({e 0}ᶜ) :=
    contMDiffOn_singular e hei χ hχ
  have hUM : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ U ({e 0}ᶜ) := by
    convert! hΦM.sub hGs using 1
    funext y
    ring
  have hcomp {f : M → ℝ} (hf : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f ({e 0}ᶜ)) :
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x => f (e x)) Ω := by
    intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    exact (hf.contMDiffAt (isOpen_compl_singleton.mem_nhds (haway hx))).comp x
      (he.contMDiffAt (e.open_source.mem_nhds (hxsource hx)))
  have hUc := hcomp hUM
  have hΦc := hcomp hΦM
  refine ⟨hUc.contDiffOn, ?_⟩
  intro x hx
  change x ∈ Ω at hx
  have hx0 : x ≠ 0 := by simpa using hx.2
  have hxr : x ∈ ball (0 : E) r := hxball hx
  have hxχ : ‖x‖ < χ.rIn := by simpa using hxinner hx
  have htransport := conformalP_eq_of_chart_coefficients_and_germ
    g gE g.leviCivitaData gE.leviCivitaData e he hei isOpen_ball
    (fun y hy => hrs (ball_subset_closedBall hy))
    (fun y hy => hcoeff y (ball_subset_closedBall hy)) hxr
    (hGs.contMDiffAt (isOpen_compl_singleton.mem_nhds (haway hx)))
    (Eventually.of_forall (fun _ : E => rfl))
  have hGlocal :
      -gE.leviCivitaData.laplacian (fun y => singular e χ (e y) - U (e y)) x +
        (gE.leviCivitaData.scalarCurvature x / 8) * (singular e χ (e x) - U (e x)) = 0 :=
    htransport.trans (hGP (e x) (haway hx))
  have hΦgerm : (fun y => singular e χ (e y)) =ᶠ[𝓝 x]
      (fun y : E => ‖y‖⁻¹) := by
    filter_upwards [isOpen_ball.mem_nhds (hxinner hx)] with y hy
    exact singular_eq_inv_norm_near_center e χ hχ (ball_subset_closedBall hy)
  have hΦP :
      -gE.leviCivitaData.laplacian (fun y => singular e χ (e y)) x +
        (gE.leviCivitaData.scalarCurvature x / 8) * singular e χ (e x) = nativeResidual gE χ x := by
    have hΦvalue : singular e χ (e x) = ‖x‖⁻¹ := hΦgerm.self_of_nhds
    rw [gE.leviCivitaData.laplacian_eq_of_eventuallyEq hΦgerm, hΦvalue,
      native_conformalP_inv_norm gE hGauss hx0, nativeResidual_eq_densityResidual_inner gE χ hxχ]
  rw [native_laplacian_sub_on gE hΩ hΦc hUc hx] at hGlocal
  linarith

#print axioms native_laplacian_sub_on
#print axioms native_correction_smooth_and_equation_in_chart

end Yamabe3.Analysis.GreenParametrix
