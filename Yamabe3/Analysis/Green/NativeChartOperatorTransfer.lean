import PoincareLib.Geometry.Riemannian.Coordinates.Coefficients
import PoincareLib.Geometry.Riemannian.ScalarOperators.Divergence.Pullback
import PoincareLib.Geometry.Riemannian.ScalarOperators.Locality
import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometryInvariants

/-!
# Native scalar operators from actual chart coefficient equality

The metric pairing and invertible differential required by the upstream
transport theorems are derived from the actual pullback coefficient equality
and a genuine smooth chart with smooth inverse. Local isometry is not an
additional input. The statements apply to the actual Gauss metric extension
constructed in `NativeNormalDensity` on its ball of agreement.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter PoincareMT
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis.ChartOperatorTransfer

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

section General

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]

/-- Equality of the actual coefficient maps is precisely preservation of
the native metric pairings by the actual chart differential. -/
theorem metric_pairing_of_coefficients
    (g : RiemannianMetric n M) (gE : RiemannianMetric n (E n))
    (e : E n → M) (x : E n)
    (hcoeff : gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    (a b : E n) :
    gE.inner x a b = g.inner (e x)
      (mfderiv (𝓡 n) (𝓡 n) e x a) (mfderiv (𝓡 n) (𝓡 n) e x b) :=
  congrArg (fun B => B a b) hcoeff

/-- The retained native Laplacians commute with the actual smooth chart
where the actual metric coefficients agree. -/
theorem laplacian_comp_of_chart_coefficients
    (g : RiemannianMetric n M) (gE : RiemannianMetric n (E n))
    (D : LeviCivitaData g) (DE : LeviCivitaData gE)
    (e : OpenPartialHomeomorph (E n) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {U : Set (E n)} (hU : IsOpen U) (hsource : U ⊆ e.source)
    (hcoeff : ∀ y ∈ U, gE.euclideanCoefficients y = g.pullbackCoefficients e y)
    {x : E n} (hx : x ∈ U) {u : M → ℝ}
    (hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ u (e x)) :
    DE.laplacian (u ∘ e) x = D.laplacian u (e x) := by
  have heD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  apply DE.laplacian_comp_of_metric_pullback D
    (he.contMDiffAt (e.open_source.mem_nhds (hsource hx))) ?_ ?_ hu
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact ⟨heD.mfderiv (hsource hy), rfl⟩
  · filter_upwards [hU.mem_nhds hx] with y hy
    intro a b
    exact metric_pairing_of_coefficients g gE e y (hcoeff y hy) a b

/-- Scalar curvature preservation follows from the actual coefficient
identity on an open set, with no separate isometry field or premise. -/
theorem scalarCurvature_eq_of_chart_coefficients
    (g : RiemannianMetric n M) (gE : RiemannianMetric n (E n))
    (D : LeviCivitaData g) (DE : LeviCivitaData gE)
    (e : OpenPartialHomeomorph (E n) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    {U : Set (E n)} (hU : IsOpen U) (hsource : U ⊆ e.source)
    (hcoeff : ∀ y ∈ U, gE.euclideanCoefficients y = g.pullbackCoefficients e y)
    {x : E n} (hx : x ∈ U) :
    DE.scalarCurvature x = D.scalarCurvature (e x) := by
  apply DE.scalarCurvature_eq_of_local_isometry D hU (he.mono hsource) ?_ hx
  intro y hy a b
  exact metric_pairing_of_coefficients g gE e y (hcoeff y hy) a b

/-- A coordinate expression need only agree with the pulled-back native
function on a genuine neighborhood. Locality removes all choices outside
the chart, as required for the actual cutoff extension. -/
theorem laplacian_eq_of_chart_coefficients_and_germ
    (g : RiemannianMetric n M) (gE : RiemannianMetric n (E n))
    (D : LeviCivitaData g) (DE : LeviCivitaData gE)
    (e : OpenPartialHomeomorph (E n) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {U : Set (E n)} (hU : IsOpen U) (hsource : U ⊆ e.source)
    (hcoeff : ∀ y ∈ U, gE.euclideanCoefficients y = g.pullbackCoefficients e y)
    {x : E n} (hx : x ∈ U) {u : M → ℝ} {v : E n → ℝ}
    (hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ u (e x))
    (hcomp : (u ∘ e) =ᶠ[𝓝 x] v) :
    DE.laplacian v x = D.laplacian u (e x) := by
  calc
    DE.laplacian v x = DE.laplacian (u ∘ e) x :=
      (DE.laplacian_eq_of_eventuallyEq hcomp).symm
    _ = D.laplacian u (e x) :=
      laplacian_comp_of_chart_coefficients g gE D DE e he hei hU hsource hcoeff hx hu

end General

section DimensionThree

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (E 3) M] [IsManifold (𝓡 3) ∞ M]

/-- The precise operator `P = -Delta + R/8` transfers from the real
Euclidean extension to the real background manifold on the chart domain.
The scalar functions may be defined arbitrarily outside their matching germ. -/
theorem conformalP_eq_of_chart_coefficients_and_germ
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 (E 3))
    (D : LeviCivitaData g) (DE : LeviCivitaData gE)
    (e : OpenPartialHomeomorph (E 3) M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {U : Set (E 3)} (hU : IsOpen U) (hsource : U ⊆ e.source)
    (hcoeff : ∀ y ∈ U, gE.euclideanCoefficients y = g.pullbackCoefficients e y)
    {x : E 3} (hx : x ∈ U) {u : M → ℝ} {v : E 3 → ℝ}
    (hu : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ u (e x))
    (hcomp : (u ∘ e) =ᶠ[𝓝 x] v) :
    -DE.laplacian v x + (DE.scalarCurvature x / 8) * v x =
      -D.laplacian u (e x) + (D.scalarCurvature (e x) / 8) * u (e x) := by
  have hvx : v x = u (e x) := hcomp.self_of_nhds.symm
  rw [laplacian_eq_of_chart_coefficients_and_germ g gE D DE e he hei hU hsource
      hcoeff hx hu hcomp,
    scalarCurvature_eq_of_chart_coefficients g gE D DE e he hU hsource hcoeff hx,
    hvx]

end DimensionThree

#print axioms metric_pairing_of_coefficients
#print axioms laplacian_comp_of_chart_coefficients
#print axioms scalarCurvature_eq_of_chart_coefficients
#print axioms laplacian_eq_of_chart_coefficients_and_germ
#print axioms conformalP_eq_of_chart_coefficients_and_germ

end Yamabe3.Analysis.ChartOperatorTransfer
