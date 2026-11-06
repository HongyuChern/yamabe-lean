import Yamabe3.Analysis.NativeSmallJacobianInverse
import Yamabe3.Analysis.GreenCorrection

/-!
# The actual closed Jacobian form on native smooth tests

This is the original native-volume test identity, separated from the
later continuous-representative regularity theorem. Its statement and
proof body are retained verbatim, with all original coefficients and
one original L2 representative. No fixed dependency source is changed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

theorem closedYamabeJacobianForm_test_eq_integral (g : RiemannianMetric 3 M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (w : H1Zero g.leviCivitaData univ) (f : EnergyTest g.leviCivitaData univ) :
    closedYamabeJacobianForm g u hu w (f : H1Zero g.leviCivitaData univ) =
      ∫ x, (-8 * g.leviCivitaData.laplacian f x +
        g.leviCivitaData.scalarCurvature x * f x - 30 * u x ^ 4 * f x) *
          toL2 g.leviCivitaData univ w x ∂g.volumeMeasure := by
  have hΔ := f.laplacian_memLp.integrable_mul (Lp.memLp (toL2 g.leviCivitaData univ w))
  have hR := (f.mulSmooth g.leviCivitaData.scalarCurvature
    g.leviCivitaData.contMDiff_scalarCurvature).memLp.integrable_mul
      (Lp.memLp (toL2 g.leviCivitaData univ w))
  have hU := (f.mulSmooth (fun x => u x ^ 4) (hu.pow 4)).memLp.integrable_mul
    (Lp.memLp (toL2 g.leviCivitaData univ w))
  have hi : Integrable (fun x =>
      (-8 * g.leviCivitaData.laplacian f x + g.leviCivitaData.scalarCurvature x * f x) *
        toL2 g.leviCivitaData univ w x) g.volumeMeasure := by
    apply ((hΔ.const_mul (-8)).add hR).congr
    filter_upwards [] with x
    simp only [EnergyTest.mulSmooth_apply, Pi.add_apply, Pi.mul_apply]
    ring
  have hj : Integrable (fun x => 30 * (u x ^ 4 * f x * toL2 g.leviCivitaData univ w x))
      g.volumeMeasure := by
    simpa only [EnergyTest.mulSmooth_apply, Pi.mul_apply] using hU.const_mul 30
  rw [closedYamabeJacobianForm_apply, closedYamabeForm_test_eq_integral,
    potentialForm_symm, potentialForm_test_eq_integral, ← integral_const_mul,
    ← integral_sub hi hj]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

#print axioms closedYamabeJacobianForm_test_eq_integral

end Yamabe3.Analysis
