import Yamabe3.Analysis.NativeJacobianTestEquation
import Yamabe3.Analysis.GreenContinuous

/-!
# The actual L2-forced Jacobian inverse has a continuous representative

The same constructed H1 inverse is identified, by the proved native weak
uniqueness, with the existing conformal-Laplacian inverse of its actual L2
effective source. This proves continuity of that same solution. It does
not assume pointwise regularity of a Hilbert-space element.
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

def jacobianEffectiveL2Source (g : RiemannianMetric 3 M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (F : Lp ℝ 2 g.volumeMeasure) (w : H1Zero g.leviCivitaData univ) : Lp ℝ 2 g.volumeMeasure :=
  (1 / 8 : ℝ) • (F + (30 : ℝ) • toL2 g.leviCivitaData univ
    (energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ)
      (fun x => u x ^ 4) (hu.pow 4) w))

theorem closedYamabeJacobianL2_resolvent_identity (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g) (F : Lp ℝ 2 g.volumeMeasure) :
    let w := closedYamabeJacobianInverse g hY u hu hsmall (closedL2Forcing g F)
    w = closedConformalLaplacianL2Solution g hY (jacobianEffectiveL2Source g u hu F w) := by
  dsimp only
  apply closedConformalLaplacianInverse_unique
  intro z
  have h := closedYamabeJacobianInverse_spec g hY u hu hsmall (closedL2Forcing g F) z
  rw [closedYamabeJacobianForm_apply, closedL2Forcing_apply, potentialForm_apply] at h
  rw [closedConformalLaplacianForm_apply, closedL2Forcing_apply,
    jacobianEffectiveL2Source, real_inner_smul_left, inner_add_left, real_inner_smul_left]
  linarith only [h]

theorem closedYamabeJacobianL2_exists_continuous_representative
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g) (F : Lp ℝ 2 g.volumeMeasure) :
    ∃ W : M → ℝ, Continuous W ∧
      W =ᵐ[g.volumeMeasure]
        (toL2 g.leviCivitaData univ
          (closedYamabeJacobianInverse g hY u hu hsmall (closedL2Forcing g F)) : M → ℝ) ∧
      ∀ f : EnergyTest g.leviCivitaData univ,
        (∫ x, (-8 * g.leviCivitaData.laplacian f x +
          g.leviCivitaData.scalarCurvature x * f x - 30 * u x ^ 4 * f x) * W x
            ∂g.volumeMeasure) = ∫ x, f x * F x ∂g.volumeMeasure := by
  let w := closedYamabeJacobianInverse g hY u hu hsmall (closedL2Forcing g F)
  have he : w = closedConformalLaplacianL2Solution g hY (jacobianEffectiveL2Source g u hu F w) :=
    closedYamabeJacobianL2_resolvent_identity g hY u hu hsmall F
  obtain ⟨W, hW, hWae⟩ := closedL2Solution_exists_continuous_representative g hY
    (jacobianEffectiveL2Source g u hu F w)
  rw [← he] at hWae
  refine ⟨W, hW, hWae, fun f => ?_⟩
  calc
    _ = ∫ x, (-8 * g.leviCivitaData.laplacian f x +
        g.leviCivitaData.scalarCurvature x * f x - 30 * u x ^ 4 * f x) *
          toL2 g.leviCivitaData univ w x ∂g.volumeMeasure := by
      apply integral_congr_ae
      filter_upwards [hWae] with x hx
      rw [hx]
    _ = _ := by
      rw [← closedYamabeJacobianForm_test_eq_integral g u hu w f,
        closedYamabeJacobianInverse_spec, closedL2Forcing_apply_test]

#print axioms closedYamabeJacobianForm_test_eq_integral
#print axioms closedYamabeJacobianL2_resolvent_identity
#print axioms closedYamabeJacobianL2_exists_continuous_representative

end Yamabe3.Analysis
