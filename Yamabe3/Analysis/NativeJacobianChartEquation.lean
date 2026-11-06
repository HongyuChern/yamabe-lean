import Yamabe3.Analysis.Green.NativeChartOperatorTransfer
import Yamabe3.Analysis.UniformElliptic.LocalDivergenceEquation

/-!
# The same native Jacobian solution in its actual normal chart

The metric is the retained extension whose coefficients agree with the
pullback of the original metric. The scalar function is the actual native
solution composed with that very chart. Its equation, including the factor
eight and the quartic potential, gives the density-weighted rescaled weak
equation used by the local derivative estimates.

No coordinate equation, normal derivative, or derivative estimate is added
as an input. Local native smoothness suffices on the stated open region.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis

open PoincareMT
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates
open UniformElliptic ChartOperatorTransfer

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]

/-- Native local smoothness gives actual Euclidean smoothness of the
same chart representative, without requiring a smooth extension over a pole. -/
theorem contDiffOn_native_chart_representative
    (e : OpenPartialHomeomorph E3 M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    {O : Set E3} (hsource : O ⊆ e.source) {W : M → ℝ}
    (hW : ∀ x ∈ O, ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ W (e x)) :
    ContDiffOn ℝ ∞ (W ∘ e) O := by
  intro x hx
  exact (contMDiffAt_iff_contDiffAt.mp ((hW x hx).comp x
    (he.contMDiffAt (e.open_source.mem_nhds (hsource hx))))).contDiffWithinAt

/-- The actual `-8 Δ + R - 30 u⁴` equation transports through the same
chart coefficient identity, with its exact division by eight. -/
theorem native_jacobian_equation_in_chart
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E3)
    (D : LeviCivitaData g) (DE : LeviCivitaData gE)
    (e : OpenPartialHomeomorph E3 M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O : Set E3} (hO : IsOpen O) (hsource : O ⊆ e.source)
    (hcoeff : ∀ x ∈ O, gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    {u W F : M → ℝ}
    (hW : ∀ x ∈ O, ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ W (e x))
    (hP : ∀ x ∈ O, -8 * D.laplacian W (e x) +
      (D.scalarCurvature (e x) - 30 * u (e x) ^ 4) * W (e x) = F (e x)) :
    ∀ x ∈ O, -DE.laplacian (W ∘ e) x +
      ((DE.scalarCurvature x - 30 * u (e x) ^ 4) / 8) * (W ∘ e) x = F (e x) / 8 := by
  intro x hx
  rw [laplacian_comp_of_chart_coefficients g gE D DE e he hei hO hsource
      hcoeff hx (hW x hx),
    scalarCurvature_eq_of_chart_coefficients g gE D DE e he hO hsource hcoeff hx]
  change -D.laplacian W (e x) +
    ((D.scalarCurvature (e x) - 30 * u (e x) ^ 4) / 8) * W (e x) = F (e x) / 8
  nlinarith only [hP x hx]

/-- The same native solution has the true weak divergence equation on
the rescaled annulus. Both source and potential retain the native density
and the exact `r² / 8` factors. The integration measure is Euclidean volume;
the native volume density has explicitly entered the two coefficients. -/
theorem native_jacobian_rescaled_weak_equation
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E3)
    (D : LeviCivitaData g) (DE : LeviCivitaData gE)
    (e : OpenPartialHomeomorph E3 M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O A V : Set E3} (hO : IsOpen O) (hA : IsOpen A) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVA : closure V ⊆ A)
    (hsource : O ⊆ e.source)
    (hcoeff : ∀ x ∈ O, gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    {u W F : M → ℝ}
    (hW : ∀ x ∈ O, ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ W (e x))
    (hP : ∀ x ∈ O, -8 * D.laplacian W (e x) +
      (D.scalarCurvature (e x) - 30 * u (e x) ^ 4) * W (e x) = F (e x))
    (r : ℝ) (hrO : MapsTo (fun z : E3 => r • z) A O) :
    WeakEquation V
      (matrixFlux (fun z => nativeDivergenceMatrix gE (r • z))
        (fun j => partialDeriv j (fun z => W (e (r • z)))))
      (fun z => (r ^ 2 * gE.pullbackVolumeDensity id (r • z) * (F (e (r • z)) / 8)) +
        (-r ^ 2 * gE.pullbackVolumeDensity id (r • z) *
          ((DE.scalarCurvature (r • z) - 30 * u (e (r • z)) ^ 4) / 8)) *
            W (e (r • z))) := by
  have hlocal := contDiffOn_native_chart_representative e he hsource hW
  have hchart := native_jacobian_equation_in_chart g gE D DE e he hei hO
    hsource hcoeff hW hP
  have hweak := weakEquation_rescaled_native_solution gE DE hO hA hV hVc hVA
    hlocal hchart r 0 hrO
  simpa only [Function.comp_apply, mul_zero, sub_zero] using hweak

#print axioms contDiffOn_native_chart_representative
#print axioms native_jacobian_equation_in_chart
#print axioms native_jacobian_rescaled_weak_equation

end Yamabe3.Analysis
