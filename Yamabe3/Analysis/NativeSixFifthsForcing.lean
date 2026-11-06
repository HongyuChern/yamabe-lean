import GreenMass.NativeEnergyL6
import Yamabe3.Analysis.NativeJacobianL2Representative
import Mathlib.MeasureTheory.Function.Holder

/-!
# Actual native L^(6/5) forcing on the same H1 completion

The native H1-to-L6 map and the genuine Holder pairing construct a
continuous forcing map with no distributional-source assumption. Its
pairing is identified with the same native L2 representative of each H1
element. On sources that also belong to L2 this is exactly the existing
L2 forcing, so the actual weak inverses coincide.

The final inverse and its uniform bound concern actual L^(6/5) sources.
No Dirac functional, singular weighted integrability, local smoothness or
weighted pointwise estimate is asserted by this module.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

/-- The genuine extended-real exponents are conjugate. The finite nonzero
denominator is handled explicitly, rather than by field normalization. -/
theorem sixFifths_holderConjugate : ENNReal.HolderConjugate (6 / 5 : ENNReal) 6 := by
  apply ENNReal.holderConjugate_iff.mpr
  have h6z : (6 : ENNReal) ≠ 0 := by norm_num
  have h6t : (6 : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.ofNat_ne_top
  rw [ENNReal.inv_div (Or.inr h6t) (Or.inr h6z)]
  calc
    (5 : ENNReal) / 6 + 6⁻¹ = (5 + 1 : ENNReal) * 6⁻¹ := by
      rw [div_eq_mul_inv, add_one_mul]
    _ = 6 * 6⁻¹ := by norm_num
    _ = 1 := ENNReal.mul_inv_cancel h6z h6t

/-- Public numerical fact for every actual L^(6/5) consumer. -/
theorem one_le_sixFifths : 1 ≤ (6 / 5 : ENNReal) := by
  letI := sixFifths_holderConjugate
  exact ENNReal.HolderConjugate.one_le (6 / 5) 6

private instance sixFifthsSource_ge_one : Fact (1 ≤ (6 / 5 : ENNReal)) :=
  ⟨one_le_sixFifths⟩

private instance sixFifthsTarget_ge_one : Fact (1 ≤ (6 : ENNReal)) :=
  ⟨by norm_num⟩

private instance sixFifthsSource_holder : ENNReal.HolderConjugate (6 / 5 : ENNReal) 6 :=
  sixFifths_holderConjugate

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

private def sixFifthsForcingH1NormedSpace (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance

attribute [local instance] sixFifthsForcingH1NormedSpace

/-- Native Holder duality composed with the already constructed native
energy embedding. Both the source norm and the output dual norm are real. -/
def closedSixFifthsForcing (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) :
    Lp ℝ (6 / 5 : ENNReal) g.volumeMeasure →L[ℝ]
      H1Zero g.leviCivitaData univ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (H1Zero g.leviCivitaData univ)
      (Lp ℝ 6 g.volumeMeasure) ℝ).flip (GreenMass.NativeEnergyL6.toL6 g hY)).comp
    ((ContinuousLinearMap.mul ℝ ℝ).lpPairing g.volumeMeasure (6 / 5) 6)

theorem closedSixFifthsForcing_apply (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (F : Lp ℝ (6 / 5 : ENNReal) g.volumeMeasure)
    (w : H1Zero g.leviCivitaData univ) :
    closedSixFifthsForcing g hY F w =
      ∫ x, F x * toL2 g.leviCivitaData univ w x ∂g.volumeMeasure := by
  change (ContinuousLinearMap.mul ℝ ℝ).lpPairing g.volumeMeasure (6 / 5) 6
    F (GreenMass.NativeEnergyL6.toL6 g hY w) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [GreenMass.NativeEnergyL6.toL6_ae_toL2 g hY w] with x hx
  change F x * (GreenMass.NativeEnergyL6.toL6 g hY w) x = _
  rw [hx]

theorem closedSixFifthsForcing_apply_test (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (F : Lp ℝ (6 / 5 : ENNReal) g.volumeMeasure)
    (φ : EnergyTest g.leviCivitaData univ) :
    closedSixFifthsForcing g hY F (φ : H1Zero g.leviCivitaData univ) =
      ∫ x, φ x * F x ∂g.volumeMeasure := by
  rw [closedSixFifthsForcing_apply, toL2_coe]
  apply integral_congr_ae
  filter_upwards [φ.memLp.coeFn_toLp] with x hx
  rw [show (testToL2 g.leviCivitaData univ φ) x = φ x from hx, mul_comm]

/-- The Holder product is genuinely integrable for the actual native
representative; the displayed integral is not merely a totalized value. -/
theorem integrable_sixFifths_mul_native_energy (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (F : Lp ℝ (6 / 5 : ENNReal) g.volumeMeasure)
    (w : H1Zero g.leviCivitaData univ) :
    Integrable (fun x => F x * toL2 g.leviCivitaData univ w x) g.volumeMeasure := by
  exact memLp_one_iff_integrable.mp
    ((ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin 1 (Lp.memLp F)
      (GreenMass.NativeEnergyL6.native_energy_memLp_six g hY w))

/-- This new source map agrees with the old L2 source map on the same
actual measurable function whenever both genuine integrabilities hold. -/
theorem closedSixFifthsForcing_eq_closedL2Forcing
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g)
    {F : M → ℝ} (hF : MemLp F (6 / 5 : ENNReal) g.volumeMeasure)
    (hF2 : MemLp F 2 g.volumeMeasure) :
    closedSixFifthsForcing g hY (hF.toLp F) = closedL2Forcing g (hF2.toLp F) := by
  ext w
  rw [closedSixFifthsForcing_apply, closedL2Forcing_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp, hF2.coeFn_toLp] with x hx hx2
  change (hF.toLp F) x * toL2 g.leviCivitaData univ w x =
    inner ℝ ((hF2.toLp F) x) (toL2 g.leviCivitaData univ w x)
  rw [hx, hx2]
  simp [mul_comm]

/-- The actual constructed Jacobian inverse, with this legitimate source
space. No new inverse existence or coercivity assumption is introduced. -/
def closedSixFifthsJacobianSolutionCLM (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g) :
    Lp ℝ (6 / 5 : ENNReal) g.volumeMeasure →L[ℝ] H1Zero g.leviCivitaData univ :=
  (closedYamabeJacobianInverse g hY u hu hsmall).comp (closedSixFifthsForcing g hY)

theorem closedSixFifthsJacobianSolution_native_test
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g)
    (F : Lp ℝ (6 / 5 : ENNReal) g.volumeMeasure)
    (φ : EnergyTest g.leviCivitaData univ) :
    (∫ x, (-8 * g.leviCivitaData.laplacian φ x +
      g.leviCivitaData.scalarCurvature x * φ x - 30 * u x ^ 4 * φ x) *
        toL2 g.leviCivitaData univ
          (closedSixFifthsJacobianSolutionCLM g hY u hu hsmall F) x ∂g.volumeMeasure) =
      ∫ x, φ x * F x ∂g.volumeMeasure := by
  rw [← closedYamabeJacobianForm_test_eq_integral]
  change closedYamabeJacobianForm g u hu
    (closedYamabeJacobianInverse g hY u hu hsmall (closedSixFifthsForcing g hY F))
      (φ : H1Zero g.leviCivitaData univ) = _
  rw [closedYamabeJacobianInverse_spec, closedSixFifthsForcing_apply_test]

theorem closedSixFifthsJacobianSolution_eq_L2
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g)
    {F : M → ℝ} (hF : MemLp F (6 / 5 : ENNReal) g.volumeMeasure)
    (hF2 : MemLp F 2 g.volumeMeasure) :
    closedSixFifthsJacobianSolutionCLM g hY u hu hsmall (hF.toLp F) =
      closedYamabeJacobianInverse g hY u hu hsmall (closedL2Forcing g (hF2.toLp F)) := by
  change closedYamabeJacobianInverse g hY u hu hsmall
    (closedSixFifthsForcing g hY (hF.toLp F)) = _
  rw [closedSixFifthsForcing_eq_closedL2Forcing g hY hF hF2]

/-- A common actual operator bound is chosen before every critically small
smooth background and every L^(6/5) source. -/
theorem exists_uniform_closedSixFifthsJacobianSolution_bound
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
      (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
        Target.yamabeConstant g),
      ‖closedSixFifthsJacobianSolutionCLM g hY u hu hsmall‖ ≤ C ∧
      ∀ F G : Lp ℝ (6 / 5 : ENNReal) g.volumeMeasure,
        ‖closedSixFifthsJacobianSolutionCLM g hY u hu hsmall F -
          closedSixFifthsJacobianSolutionCLM g hY u hu hsmall G‖ ≤ C * ‖F - G‖ := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_uniform_closedYamabeJacobianInverse_bound g hY
  let C := C₀ * (‖closedSixFifthsForcing g hY‖ + 1)
  have hC : 0 < C := mul_pos hC₀ (by positivity)
  refine ⟨C, hC, ?_⟩
  intro u hu hsmall
  have hnorm : ‖closedSixFifthsJacobianSolutionCLM g hY u hu hsmall‖ ≤ C := by
    calc
      _ ≤ ‖closedYamabeJacobianInverse g hY u hu hsmall‖ *
          ‖closedSixFifthsForcing g hY‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C₀ * ‖closedSixFifthsForcing g hY‖ :=
        mul_le_mul_of_nonneg_right (hbound u hu hsmall).1
          (ContinuousLinearMap.opNorm_nonneg _)
      _ ≤ C := by dsimp only [C]; nlinarith only [hC₀]
  refine ⟨hnorm, ?_⟩
  intro F G
  rw [← map_sub]
  exact ((closedSixFifthsJacobianSolutionCLM g hY u hu hsmall).le_opNorm (F - G)).trans
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

#print axioms sixFifths_holderConjugate
#print axioms one_le_sixFifths
#print axioms closedSixFifthsForcing_apply
#print axioms integrable_sixFifths_mul_native_energy
#print axioms closedSixFifthsForcing_eq_closedL2Forcing
#print axioms closedSixFifthsJacobianSolution_native_test
#print axioms exists_uniform_closedSixFifthsJacobianSolution_bound

end Yamabe3.Analysis
