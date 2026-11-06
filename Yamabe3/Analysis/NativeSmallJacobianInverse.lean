import Yamabe3.Analysis.NativeCriticalPotential

/-!
# A uniform native weak inverse for critically small backgrounds

The true quartic potential estimate proves coercivity. Lax--Milgram
constructs the bounded linear inverse on the actual native H1 dual.
The inverse bound is chosen before the background. Instantiating the
smallness condition on a truncated Green exterior is a separate step;
this closed-manifold block is not a punctured weighted global inverse.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

local instance (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance

theorem closedYamabeJacobianForm_isCoercive (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g) : IsCoercive (closedYamabeJacobianForm g u hu) := by
  obtain ⟨κ, hκ, hcoer⟩ := exists_uniform_closedYamabeJacobian_coercivity g hY
  refine ⟨κ, hκ, fun w => ?_⟩
  simpa only [pow_two, mul_assoc] using hcoer u hu hsmall w

def closedYamabeJacobianInverse (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g) :
    (H1Zero g.leviCivitaData univ →L[ℝ] ℝ) →L[ℝ] H1Zero g.leviCivitaData univ :=
  (closedYamabeJacobianForm_isCoercive g hY u hu hsmall).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
      (InnerProductSpace.toDual ℝ (H1Zero g.leviCivitaData univ)).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem closedYamabeJacobianInverse_spec (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g)
    (ell : H1Zero g.leviCivitaData univ →L[ℝ] ℝ)
    (w : H1Zero g.leviCivitaData univ) :
    closedYamabeJacobianForm g u hu (closedYamabeJacobianInverse g hY u hu hsmall ell) w =
      ell w := by
  rw [← (closedYamabeJacobianForm_isCoercive g hY u hu hsmall).continuousLinearEquivOfBilin_apply]
  simp only [closedYamabeJacobianInverse, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  exact InnerProductSpace.toDual_symm_apply

theorem closedYamabeJacobianInverse_unique (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g)
    (ell : H1Zero g.leviCivitaData univ →L[ℝ] ℝ)
    (w : H1Zero g.leviCivitaData univ)
    (hw : ∀ z, closedYamabeJacobianForm g u hu w z = ell z) :
    w = closedYamabeJacobianInverse g hY u hu hsmall ell := by
  apply (closedYamabeJacobianForm_isCoercive g hY u hu hsmall).continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro z
  rw [(closedYamabeJacobianForm_isCoercive g hY u hu hsmall).continuousLinearEquivOfBilin_apply,
    (closedYamabeJacobianForm_isCoercive g hY u hu hsmall).continuousLinearEquivOfBilin_apply,
    hw, closedYamabeJacobianInverse_spec]

theorem exists_uniform_closedYamabeJacobianInverse_bound (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
      (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
        Target.yamabeConstant g),
      ‖closedYamabeJacobianInverse g hY u hu hsmall‖ ≤ C ∧
      ∀ ell₁ ell₂ : H1Zero g.leviCivitaData univ →L[ℝ] ℝ,
        ‖closedYamabeJacobianInverse g hY u hu hsmall ell₁ -
          closedYamabeJacobianInverse g hY u hu hsmall ell₂‖ ≤ C * ‖ell₁ - ell₂‖ := by
  obtain ⟨κ, hκ, hcoer⟩ := exists_uniform_closedYamabeJacobian_coercivity g hY
  refine ⟨κ⁻¹, inv_pos.mpr hκ, fun u hu hsmall => ?_⟩
  let R := closedYamabeJacobianInverse g hY u hu hsmall
  have hbound (ell : H1Zero g.leviCivitaData univ →L[ℝ] ℝ) :
      ‖R ell‖ ≤ κ⁻¹ * ‖ell‖ := by
    have h0 : 0 ≤ ‖R ell‖ := norm_nonneg _
    by_cases hz : ‖R ell‖ = 0
    · rw [hz]
      positivity
    · have hp : 0 < ‖R ell‖ := lt_of_le_of_ne h0 (Ne.symm hz)
      have he := hcoer u hu hsmall (R ell)
      rw [closedYamabeJacobianInverse_spec] at he
      have he' := he.trans ((le_abs_self _).trans (ell.le_opNorm (R ell)))
      have hc : κ * ‖R ell‖ ≤ ‖ell‖ :=
        (mul_le_mul_iff_right₀ hp).mp (by convert he' using 1 <;> ring)
      calc
        ‖R ell‖ ≤ ‖ell‖ / κ := (le_div_iff₀ hκ).mpr (by simpa only [mul_comm] using hc)
        _ = κ⁻¹ * ‖ell‖ := by ring
  refine ⟨ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hκ.le) hbound, ?_⟩
  intro ell₁ ell₂
  simpa only [map_sub] using hbound (ell₁ - ell₂)

#print axioms closedYamabeJacobianForm_isCoercive
#print axioms closedYamabeJacobianInverse_spec
#print axioms closedYamabeJacobianInverse_unique
#print axioms exists_uniform_closedYamabeJacobianInverse_bound

end Yamabe3.Analysis
