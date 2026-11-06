import Yamabe3.Analysis.Green.NativeChartOperatorTransfer
import Yamabe3.Analysis.Green.NativeCutoffParametrix

/-!
# Native operator transfer for the actual chart cutoff potentials

The functions on the background manifold are the actual smooth extensions
by zero, and the coefficient equality supplies their operator transport.
No local-isometry premise or desired source equation is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareMT
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis.ChartOperatorTransfer

open Yamabe3.Parametrix

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (E 3) M] [IsManifold (𝓡 3) ∞ M]

/-- The actual regularized cutoff function on the manifold is transported
to the explicit Euclidean cutoff by the native operator `-Delta + R/8`. -/
theorem regularized_conformalP_transfer
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 (E 3))
    (D : LeviCivitaData g) (DE : LeviCivitaData gE)
    (e : OpenPartialHomeomorph (E 3) M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {U : Set (E 3)} (hU : IsOpen U) (hsource : U ⊆ e.source)
    (hcoeff : ∀ y ∈ U, gE.euclideanCoefficients y = g.pullbackCoefficients e y)
    (χ : ContDiffBump (0 : E 3)) (hχ : tsupport χ ⊆ e.source)
    {ε : ℝ} (hε : 0 < ε) {x : E 3} (hx : x ∈ U) :
    -D.laplacian (regularized e χ ε) (e x) +
        (D.scalarCurvature (e x) / 8) * regularized e χ ε (e x) =
      -DE.laplacian (cutoffRegularized χ ε) x +
        (DE.scalarCurvature x / 8) * cutoffRegularized χ ε x := by
  exact (conformalP_eq_of_chart_coefficients_and_germ g gE D DE e he hei hU hsource
    hcoeff hx (contMDiff_regularized e hei χ hχ hε (e x))
    (regularized_comp_eventuallyEq e χ ε (hsource hx))).symm

/-- The same actual native operator identity holds for the singular cutoff
at every nonzero chart point. It makes no pointwise claim at the pole. -/
theorem singular_conformalP_transfer
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 (E 3))
    (D : LeviCivitaData g) (DE : LeviCivitaData gE)
    (e : OpenPartialHomeomorph (E 3) M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (he0 : (0 : E 3) ∈ e.source)
    {U : Set (E 3)} (hU : IsOpen U) (hsource : U ⊆ e.source)
    (hcoeff : ∀ y ∈ U, gE.euclideanCoefficients y = g.pullbackCoefficients e y)
    (χ : ContDiffBump (0 : E 3)) (hχ : tsupport χ ⊆ e.source)
    {x : E 3} (hx : x ∈ U) (hx0 : x ≠ 0) :
    -D.laplacian (singular e χ) (e x) +
        (D.scalarCurvature (e x) / 8) * singular e χ (e x) =
      -DE.laplacian (cutoffSingular χ) x +
        (DE.scalarCurvature x / 8) * cutoffSingular χ x := by
  have hxp : e x ≠ e 0 := by
    intro h
    exact hx0 (e.injOn (hsource hx) he0 h)
  exact (conformalP_eq_of_chart_coefficients_and_germ g gE D DE e he hei hU hsource
    hcoeff hx (contMDiffAt_singular e hei χ hχ hxp)
    (singular_comp_eventuallyEq e χ (hsource hx))).symm

#print axioms regularized_conformalP_transfer
#print axioms singular_conformalP_transfer

end Yamabe3.Analysis.ChartOperatorTransfer
