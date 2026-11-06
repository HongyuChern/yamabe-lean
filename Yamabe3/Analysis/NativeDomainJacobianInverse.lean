import Yamabe3.Analysis.NativeJacobianTestEquation
import Yamabe3.Analysis.NativeDomainEnergyInclusionCore

/-!
# A genuine zero-boundary native Jacobian inverse on every domain

The actual completion of compactly supported smooth functions in a domain
embeds isometrically into the closed energy space. Restricting the proved
closed Yamabe Jacobian form through this inclusion gives uniform coercivity,
then Lax--Milgram constructs the actual H1-zero weak inverse. The constant
is chosen before the domain and the critically small smooth background.

The actual inclusion is imported from NativeDomainEnergyInclusionCore,
where the original proof bodies are retained and the same maps are proved
equal to the fixed Poincare inclusions. No fixed dependency source is changed.

The L2 solution below is the same energy solution, with its genuine native
transposed test equation and almost-everywhere zero extension outside the
domain. Boundary continuity, a classical normal derivative, weighted estimates,
and matching on a glued manifold are not conclusions of this module.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

private def domainJacobianH1NormedSpace (g : RiemannianMetric 3 M) (Ω : Set M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData Ω) := inferInstance
attribute [local instance] domainJacobianH1NormedSpace

/-- The actual closed Jacobian form restricted along the energy isometry. -/
def domainYamabeJacobianForm (g : RiemannianMetric 3 M) (Ω : Set M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u) :
    H1Zero g.leviCivitaData Ω →L[ℝ] H1Zero g.leviCivitaData Ω →L[ℝ] ℝ :=
  (closedYamabeJacobianForm g u hu).bilinearComp
    (nativeDomainEnergyInclusion g Ω) (nativeDomainEnergyInclusion g Ω)

@[simp] theorem domainYamabeJacobianForm_apply (g : RiemannianMetric 3 M) (Ω : Set M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (w z : H1Zero g.leviCivitaData Ω) :
    domainYamabeJacobianForm g Ω u hu w z =
      closedYamabeJacobianForm g u hu (nativeDomainEnergyInclusion g Ω w)
        (nativeDomainEnergyInclusion g Ω z) := rfl

theorem domainYamabeJacobianForm_coe (g : RiemannianMetric 3 M) (Ω : Set M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (f h : EnergyTest g.leviCivitaData Ω) :
    domainYamabeJacobianForm g Ω u hu (f : H1Zero g.leviCivitaData Ω)
      (h : H1Zero g.leviCivitaData Ω) =
      ∫ x, (8 * g.inner x (g.leviCivitaData.gradient f x)
          (g.leviCivitaData.gradient h x) +
        (g.leviCivitaData.scalarCurvature x - 30 * u x ^ 4) * f x * h x)
          ∂g.volumeMeasure := by
  rw [domainYamabeJacobianForm_apply, nativeDomainEnergyInclusion_coe,
    nativeDomainEnergyInclusion_coe, closedYamabeJacobianForm_coe]
  rfl

/-- Every compactly supported smooth test in the domain is retained. -/
theorem domainYamabeJacobianForm_test_eq_integral
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (w : H1Zero g.leviCivitaData Ω) (f : EnergyTest g.leviCivitaData Ω) :
    domainYamabeJacobianForm g Ω u hu w (f : H1Zero g.leviCivitaData Ω) =
      ∫ x, (-8 * g.leviCivitaData.laplacian f x +
        g.leviCivitaData.scalarCurvature x * f x - 30 * u x ^ 4 * f x) *
          toL2 g.leviCivitaData Ω w x ∂g.volumeMeasure := by
  rw [domainYamabeJacobianForm_apply, nativeDomainEnergyInclusion_coe,
    closedYamabeJacobianForm_test_eq_integral, nativeDomainEnergyInclusion_toL2]
  rfl

/-- A positive coercivity constant precedes all domains and backgrounds. -/
theorem exists_uniform_domainYamabeJacobian_coercivity (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (Ω : Set M) (u : M → ℝ)
      (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u),
      60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤ Target.yamabeConstant g →
      ∀ w : H1Zero g.leviCivitaData Ω,
        κ * ‖w‖ ^ 2 ≤ domainYamabeJacobianForm g Ω u hu w w := by
  obtain ⟨κ, hκ, hcoer⟩ := exists_uniform_closedYamabeJacobian_coercivity g hY
  refine ⟨κ, hκ, fun Ω u hu hsmall w => ?_⟩
  simpa only [domainYamabeJacobianForm_apply, norm_nativeDomainEnergyInclusion] using
    hcoer u hu hsmall (nativeDomainEnergyInclusion g Ω w)

theorem domainYamabeJacobianForm_isCoercive (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (Ω : Set M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g) : IsCoercive (domainYamabeJacobianForm g Ω u hu) := by
  obtain ⟨κ, hκ, hcoer⟩ := exists_uniform_domainYamabeJacobian_coercivity g hY
  refine ⟨κ, hκ, fun w => ?_⟩
  simpa only [pow_two, mul_assoc] using hcoer Ω u hu hsmall w

def domainYamabeJacobianInverse (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (Ω : Set M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g) :
    (H1Zero g.leviCivitaData Ω →L[ℝ] ℝ) →L[ℝ] H1Zero g.leviCivitaData Ω :=
  (domainYamabeJacobianForm_isCoercive g hY Ω u hu hsmall).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (InnerProductSpace.toDual ℝ (H1Zero g.leviCivitaData Ω)).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem domainYamabeJacobianInverse_spec (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (Ω : Set M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g)
    (ell : H1Zero g.leviCivitaData Ω →L[ℝ] ℝ) (z : H1Zero g.leviCivitaData Ω) :
    domainYamabeJacobianForm g Ω u hu (domainYamabeJacobianInverse g hY Ω u hu hsmall ell) z =
      ell z := by
  rw [← (domainYamabeJacobianForm_isCoercive g hY Ω u hu hsmall).continuousLinearEquivOfBilin_apply]
  simp only [domainYamabeJacobianInverse, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  exact InnerProductSpace.toDual_symm_apply

theorem domainYamabeJacobianInverse_unique (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (Ω : Set M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g)
    (ell : H1Zero g.leviCivitaData Ω →L[ℝ] ℝ) (w : H1Zero g.leviCivitaData Ω)
    (hw : ∀ z, domainYamabeJacobianForm g Ω u hu w z = ell z) :
    w = domainYamabeJacobianInverse g hY Ω u hu hsmall ell := by
  apply (domainYamabeJacobianForm_isCoercive g hY Ω u hu hsmall).continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro z
  rw [(domainYamabeJacobianForm_isCoercive g hY Ω u hu hsmall).continuousLinearEquivOfBilin_apply,
    (domainYamabeJacobianForm_isCoercive g hY Ω u hu hsmall).continuousLinearEquivOfBilin_apply,
    hw, domainYamabeJacobianInverse_spec]

theorem exists_uniform_domainYamabeJacobianInverse_bound (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Set M) (u : M → ℝ)
      (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
      (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
        Target.yamabeConstant g),
      ‖domainYamabeJacobianInverse g hY Ω u hu hsmall‖ ≤ C ∧
      ∀ ell₁ ell₂ : H1Zero g.leviCivitaData Ω →L[ℝ] ℝ,
        ‖domainYamabeJacobianInverse g hY Ω u hu hsmall ell₁ -
          domainYamabeJacobianInverse g hY Ω u hu hsmall ell₂‖ ≤ C * ‖ell₁ - ell₂‖ := by
  obtain ⟨κ, hκ, hcoer⟩ := exists_uniform_domainYamabeJacobian_coercivity g hY
  refine ⟨κ⁻¹, inv_pos.mpr hκ, fun Ω u hu hsmall => ?_⟩
  let R := domainYamabeJacobianInverse g hY Ω u hu hsmall
  have hbound (ell : H1Zero g.leviCivitaData Ω →L[ℝ] ℝ) : ‖R ell‖ ≤ κ⁻¹ * ‖ell‖ := by
    have h0 : 0 ≤ ‖R ell‖ := norm_nonneg _
    by_cases hz : ‖R ell‖ = 0
    · rw [hz]
      positivity
    · have hp : 0 < ‖R ell‖ := lt_of_le_of_ne h0 (Ne.symm hz)
      have he := hcoer Ω u hu hsmall (R ell)
      rw [domainYamabeJacobianInverse_spec] at he
      have he' := he.trans ((le_abs_self _).trans (ell.le_opNorm (R ell)))
      have hc : κ * ‖R ell‖ ≤ ‖ell‖ :=
        (mul_le_mul_iff_right₀ hp).mp (by convert he' using 1 <;> ring)
      calc
        ‖R ell‖ ≤ ‖ell‖ / κ := (le_div_iff₀ hκ).mpr (by simpa only [mul_comm] using hc)
        _ = κ⁻¹ * ‖ell‖ := by ring
  refine ⟨ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hκ.le) hbound, ?_⟩
  intro ell₁ ell₂
  simpa only [map_sub] using hbound (ell₁ - ell₂)

/-- The L2 source pairing uses the original Riemannian volume and actual inclusion. -/
def nativeDomainL2Forcing (g : RiemannianMetric 3 M) (Ω : Set M) :
    Lp ℝ 2 g.volumeMeasure →L[ℝ] H1Zero g.leviCivitaData Ω →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ (Lp ℝ 2 g.volumeMeasure))
    (toL2 g.leviCivitaData Ω)

@[simp] theorem nativeDomainL2Forcing_apply (g : RiemannianMetric 3 M)
    (Ω : Set M) (F : Lp ℝ 2 g.volumeMeasure) (w : H1Zero g.leviCivitaData Ω) :
    nativeDomainL2Forcing g Ω F w = ⟪F, toL2 g.leviCivitaData Ω w⟫_ℝ := rfl

theorem norm_nativeDomainL2Forcing_le (g : RiemannianMetric 3 M)
    (Ω : Set M) (F : Lp ℝ 2 g.volumeMeasure) : ‖nativeDomainL2Forcing g Ω F‖ ≤ ‖F‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
  intro w
  exact (norm_inner_le_norm F (toL2 g.leviCivitaData Ω w)).trans
    (mul_le_mul_of_nonneg_left (norm_toL2_le w) (norm_nonneg F))

theorem nativeDomainL2Forcing_apply_test (g : RiemannianMetric 3 M)
    (Ω : Set M) (F : Lp ℝ 2 g.volumeMeasure) (f : EnergyTest g.leviCivitaData Ω) :
    nativeDomainL2Forcing g Ω F (f : H1Zero g.leviCivitaData Ω) =
      ∫ x, f x * F x ∂g.volumeMeasure := by
  have h := closedL2Forcing_apply_test g F (nativeDomainTestInclusion g Ω f)
  simpa only [closedL2Forcing_apply, ← nativeDomainEnergyInclusion_coe,
    nativeDomainEnergyInclusion_toL2, nativeDomainL2Forcing_apply,
    nativeDomainTestInclusion_apply] using h

def domainYamabeJacobianL2Inverse (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (Ω : Set M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g) : Lp ℝ 2 g.volumeMeasure →L[ℝ] H1Zero g.leviCivitaData Ω :=
  (domainYamabeJacobianInverse g hY Ω u hu hsmall).comp (nativeDomainL2Forcing g Ω)

/-- The same zero-boundary H1 solution satisfies every genuine compactly supported
smooth native test equation in the domain. The inverse constant is independent
of the domain, and the zero extension is asserted only almost everywhere. -/
theorem exists_uniform_native_domain_jacobian_L2_inverse
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Set M) (hΩ : IsOpen Ω)
      (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
      (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
        Target.yamabeConstant g),
      ‖domainYamabeJacobianL2Inverse g hY Ω u hu hsmall‖ ≤ C ∧
      ∀ F : Lp ℝ 2 g.volumeMeasure,
        let w := domainYamabeJacobianL2Inverse g hY Ω u hu hsmall F
        (∀ᵐ x ∂g.volumeMeasure, x ∉ Ω → toL2 g.leviCivitaData Ω w x = 0) ∧
        (∀ z : H1Zero g.leviCivitaData Ω,
          domainYamabeJacobianForm g Ω u hu w z = nativeDomainL2Forcing g Ω F z) ∧
        (∀ φ : EnergyTest g.leviCivitaData Ω,
          (∫ x, (-8 * g.leviCivitaData.laplacian φ x +
            g.leviCivitaData.scalarCurvature x * φ x - 30 * u x ^ 4 * φ x) *
              toL2 g.leviCivitaData Ω w x ∂g.volumeMeasure) =
            ∫ x, φ x * F x ∂g.volumeMeasure) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_domainYamabeJacobianInverse_bound g hY
  refine ⟨C, hC, fun Ω hΩ u hu hsmall => ?_⟩
  have hR := (hbound Ω u hu hsmall).1
  refine ⟨ContinuousLinearMap.opNorm_le_bound _ hC.le (fun F => ?_), ?_⟩
  · exact ((domainYamabeJacobianInverse g hY Ω u hu hsmall).le_opNorm
      (nativeDomainL2Forcing g Ω F)).trans
      ((mul_le_mul_of_nonneg_right hR (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (norm_nativeDomainL2Forcing_le g Ω F) hC.le))
  · intro F
    dsimp only
    refine ⟨toL2_ae_zero_outside hΩ.measurableSet _, ?_, ?_⟩
    · intro z
      exact domainYamabeJacobianInverse_spec g hY Ω u hu hsmall _ z
    · intro φ
      rw [← domainYamabeJacobianForm_test_eq_integral]
      exact (domainYamabeJacobianInverse_spec g hY Ω u hu hsmall _ φ).trans
        (nativeDomainL2Forcing_apply_test g Ω F φ)

#print axioms norm_nativeDomainEnergyInclusion
#print axioms domainYamabeJacobianForm_coe
#print axioms exists_uniform_domainYamabeJacobianInverse_bound
#print axioms exists_uniform_native_domain_jacobian_L2_inverse

end Yamabe3.Analysis
