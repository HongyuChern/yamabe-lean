import Yamabe3.Analysis.Green.NativeManifoldParametrix
import Yamabe3.Analysis.GreenCorrection

/-!
# Actual normalized distributional Green existence

The only analytic positivity input is the retained true Yamabe constant.
The point-source parametrix and its L2 residual are constructed, and only
that residual is passed to the native H1 inverse. Smoothness away from the
pole and pointwise positivity are separate subsequent obligations.
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet
open Yamabe3.Parametrix

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

/-- Positive true Yamabe constant yields an actual L2 distributional Green
function normalized by `P_g G_p = 4 pi delta_p`. There is no Green,
parametrix, residual, coordinate, or right-inverse existence assumption. -/
theorem exists_native_distributional_green (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (p : M) :
    ∃ G : M → ℝ, MemLp G 2 g.volumeMeasure ∧
      ∀ φ : EnergyTest g.leviCivitaData univ,
        (∫ x, (-g.leviCivitaData.laplacian φ x +
          (g.leviCivitaData.scalarCurvature x / 8) * φ x) * G x
            ∂g.volumeMeasure) = 4 * Real.pi * φ p := by
  obtain ⟨e, χ, F, _, _, _, _, hΦ, hF, hparam⟩ :=
    exists_native_pointSource_parametrix g p
  exact ⟨_, parametrix_sub_L2Solution_test g hY p (singular e χ) F hΦ hF hparam⟩

#print exists_native_distributional_green
#print axioms exists_native_distributional_green

end Yamabe3.Analysis.GreenParametrix
