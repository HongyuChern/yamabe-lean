import Yamabe3.Analysis.YamabeEnergy
import Yamabe3.Analysis.FiniteVolumeHolder
import Yamabe3.Analysis.PotentialForm
import PoincareLib.Geometry.Riemannian.Surface.Regularity
import PoincareLib.Geometry.Riemannian.Measure.LocalFinite

/-!
# Native H1 coercivity from the genuine positive Yamabe constant

The form in this file has the actual retained scalar curvature as potential
and diffusion coefficient 8. Its smooth-test gap is derived from the actual
Yamabe quotient and finite-volume Holder inequality. No gap, inverse, or
nondegeneracy estimate is supplied as an additional geometric hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace Yamabe3.Analysis

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

/-- The genuine closed-manifold Yamabe energy on the retained H1 completion. -/
def closedYamabeForm (g : RiemannianMetric 3 M) :
    H1Zero g.leviCivitaData univ →L[ℝ]
      H1Zero g.leviCivitaData univ →L[ℝ] ℝ :=
  schrodingerForm g.leviCivitaData univ (by simpa using isCompact_univ)
    8 g.leviCivitaData.scalarCurvature g.leviCivitaData.contMDiff_scalarCurvature

omit [ConnectedSpace M] in
theorem closedYamabeForm_coe (g : RiemannianMetric 3 M)
    (f : EnergyTest g.leviCivitaData univ) :
    closedYamabeForm g (f : H1Zero g.leviCivitaData univ)
      (f : H1Zero g.leviCivitaData univ) = Target.energy g (f : M → ℝ) := by
  unfold closedYamabeForm
  rw [schrodingerForm_coe]
  unfold Target.energy
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

omit [CompactSpace M] in
/-- Positivity of the actual quotient infimum implies positive total
volume, witnessed by the constant smooth test 1. -/
theorem volume_pos_of_yamabe_pos (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) : 0 < (g.volumeMeasure univ).toReal := by
  classical
  have hne : (fun _ : M => (1 : ℝ)) ≠ 0 := by
    intro h
    have hx := congrFun h (Classical.arbitrary M)
    norm_num at hx
  have h := Target.critical_denominator_pos_of_yamabe_pos g hY contMDiff_const hne
  have hden : (∫ _ : M, |(1 : ℝ)| ^ 6 ∂g.volumeMeasure) =
      (g.volumeMeasure univ).toReal := by simp [measureReal_def]
  rw [hden] at h
  by_contra hpos
  have hz : (g.volumeMeasure univ).toReal = 0 :=
    le_antisymm (not_lt.mp hpos) ENNReal.toReal_nonneg
  rw [hz, Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0)] at h
  exact (lt_irrefl 0) h

/-- The L2 spectral gap is proved on all genuine energy tests from
Yamabe positivity, with its exact total-volume factor. -/
theorem closedYamabeForm_test_L2_lower (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (f : EnergyTest g.leviCivitaData univ) :
    (Target.yamabeConstant g / (g.volumeMeasure univ).toReal ^ (2 / 3 : ℝ)) *
      ‖testToL2 g.leviCivitaData univ f‖ ^ 2 ≤
        closedYamabeForm g (f : H1Zero g.leviCivitaData univ)
          (f : H1Zero g.leviCivitaData univ) := by
  let : IsFiniteMeasure g.volumeMeasure :=
    ⟨g.volumeMeasure_lt_top_of_isCompact isCompact_univ⟩
  have hvol : 0 < (g.volumeMeasure univ).toReal ^ (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (volume_pos_of_yamabe_pos g hY) _
  by_cases hzero : (f : M → ℝ) = 0
  · have hf : f = 0 := Subtype.ext hzero
    rw [hf, Completion.coe_zero]
    simp
  · have hf6 : MemLp (f : M → ℝ) 6 g.volumeMeasure :=
      f.smooth.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
    have hholder := integral_sq_le_volume_mul_integral_six hf6
    have hnorm : ‖testToL2 g.leviCivitaData univ f‖ ^ 2 =
        ∫ x, |f x| ^ 2 ∂g.volumeMeasure := by
      rw [← real_inner_self_eq_norm_sq, testToL2_inner]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change f x * f x = |f x| ^ 2
        rw [sq_abs]
        ring
    have henergy := Target.energy_lower_bound g hY f.smooth hzero
    have hcombined : Target.yamabeConstant g *
        ‖testToL2 g.leviCivitaData univ f‖ ^ 2 ≤
          (g.volumeMeasure univ).toReal ^ (2 / 3 : ℝ) * Target.energy g (f : M → ℝ) := by
      rw [hnorm]
      calc
        Target.yamabeConstant g * (∫ x, |f x| ^ 2 ∂g.volumeMeasure) ≤
            Target.yamabeConstant g * ((g.volumeMeasure univ).toReal ^ (2 / 3 : ℝ) *
              (∫ x, |f x| ^ 6 ∂g.volumeMeasure) ^ (1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hholder (le_of_lt hY)
        _ = (g.volumeMeasure univ).toReal ^ (2 / 3 : ℝ) *
            (Target.yamabeConstant g *
              (∫ x, |f x| ^ 6 ∂g.volumeMeasure) ^ (1 / 3 : ℝ)) := by ring
        _ ≤ (g.volumeMeasure univ).toReal ^ (2 / 3 : ℝ) * Target.energy g (f : M → ℝ) :=
          mul_le_mul_of_nonneg_left henergy (le_of_lt hvol)
    rw [closedYamabeForm_coe]
    calc
      (Target.yamabeConstant g / (g.volumeMeasure univ).toReal ^ (2 / 3 : ℝ)) *
          ‖testToL2 g.leviCivitaData univ f‖ ^ 2 =
            (Target.yamabeConstant g * ‖testToL2 g.leviCivitaData univ f‖ ^ 2) /
              (g.volumeMeasure univ).toReal ^ (2 / 3 : ℝ) := by ring
      _ ≤ Target.energy g (f : M → ℝ) :=
        (div_le_iff₀ hvol).mpr (by simpa only [mul_comm] using hcombined)

/-- The native closed Yamabe form is H1-coercive under exactly the
positive-Yamabe assumption from the frozen target. -/
theorem closedYamabeForm_isCoercive (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) : IsCoercive (closedYamabeForm g) := by
  obtain ⟨B, hB, hVB⟩ := exists_nonneg_potential_lower_bound
    g.leviCivitaData.scalarCurvature g.leviCivitaData.continuous_scalarCurvature
  apply schrodingerForm_isCoercive_of_testL2_lower g.leviCivitaData univ
    (by simpa using isCompact_univ) 8
    (Target.yamabeConstant g / (g.volumeMeasure univ).toReal ^ (2 / 3 : ℝ)) B
    g.leviCivitaData.scalarCurvature g.leviCivitaData.contMDiff_scalarCurvature
    (by norm_num) (div_pos hY (Real.rpow_pos_of_pos (volume_pos_of_yamabe_pos g hY) _)) hB hVB
  exact closedYamabeForm_test_L2_lower g hY

/-- The actual continuous weak inverse of `-8 Δ + R`, constructed by
Lax--Milgram from the proven native coercivity theorem. -/
def closedYamabeInverse (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) :
    (H1Zero g.leviCivitaData univ →L[ℝ] ℝ) →L[ℝ]
      H1Zero g.leviCivitaData univ :=
  (closedYamabeForm_isCoercive g hY).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (InnerProductSpace.toDual ℝ (H1Zero g.leviCivitaData univ)).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem closedYamabeInverse_spec (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (ell : H1Zero g.leviCivitaData univ →L[ℝ] ℝ)
    (v : H1Zero g.leviCivitaData univ) :
    closedYamabeForm g (closedYamabeInverse g hY ell) v = ell v := by
  rw [← (closedYamabeForm_isCoercive g hY).continuousLinearEquivOfBilin_apply]
  simp only [closedYamabeInverse, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  exact InnerProductSpace.toDual_symm_apply

theorem closedYamabeInverse_unique (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (ell : H1Zero g.leviCivitaData univ →L[ℝ] ℝ)
    (w : H1Zero g.leviCivitaData univ)
    (hw : ∀ v, closedYamabeForm g w v = ell v) :
    w = closedYamabeInverse g hY ell := by
  apply (closedYamabeForm_isCoercive g hY).continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  rw [(closedYamabeForm_isCoercive g hY).continuousLinearEquivOfBilin_apply,
    (closedYamabeForm_isCoercive g hY).continuousLinearEquivOfBilin_apply,
    hw, closedYamabeInverse_spec]

theorem existsUnique_closedYamabe_weakSolution (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (ell : H1Zero g.leviCivitaData univ →L[ℝ] ℝ) :
    ∃! w : H1Zero g.leviCivitaData univ,
      ∀ v, closedYamabeForm g w v = ell v :=
  ⟨closedYamabeInverse g hY ell, closedYamabeInverse_spec g hY ell,
    fun w hw => closedYamabeInverse_unique g hY ell w hw⟩

/-- The manuscript normalization `P_g = -Δ_g + R_g/8`. -/
def closedConformalLaplacianForm (g : RiemannianMetric 3 M) :
    H1Zero g.leviCivitaData univ →L[ℝ]
      H1Zero g.leviCivitaData univ →L[ℝ] ℝ :=
  (1 / 8 : ℝ) • closedYamabeForm g

omit [ConnectedSpace M] in
@[simp] theorem closedConformalLaplacianForm_apply (g : RiemannianMetric 3 M)
    (v w : H1Zero g.leviCivitaData univ) :
    closedConformalLaplacianForm g v w = (1 / 8 : ℝ) * closedYamabeForm g v w := rfl

omit [ConnectedSpace M] in
theorem closedConformalLaplacianForm_coe (g : RiemannianMetric 3 M)
    (f h : EnergyTest g.leviCivitaData univ) :
    closedConformalLaplacianForm g (f : H1Zero g.leviCivitaData univ)
      (h : H1Zero g.leviCivitaData univ) =
      ∫ x, (g.inner x (g.leviCivitaData.gradient f x) (g.leviCivitaData.gradient h x) +
        (g.leviCivitaData.scalarCurvature x / 8) * f x * h x) ∂g.volumeMeasure := by
  change (1 / 8 : ℝ) * closedYamabeForm g (f : H1Zero g.leviCivitaData univ)
    (h : H1Zero g.leviCivitaData univ) = _
  unfold closedYamabeForm
  rw [schrodingerForm_coe, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

/-- The genuine weak inverse in the manuscript's normalization. -/
def closedConformalLaplacianInverse (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) :
    (H1Zero g.leviCivitaData univ →L[ℝ] ℝ) →L[ℝ]
      H1Zero g.leviCivitaData univ :=
  (closedYamabeInverse g hY).comp
    ((8 : ℝ) • ContinuousLinearMap.id ℝ (H1Zero g.leviCivitaData univ →L[ℝ] ℝ))

@[simp] theorem closedConformalLaplacianInverse_apply (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (ell : H1Zero g.leviCivitaData univ →L[ℝ] ℝ) :
    closedConformalLaplacianInverse g hY ell = closedYamabeInverse g hY ((8 : ℝ) • ell) := by
  simp only [closedConformalLaplacianInverse, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply]

theorem closedConformalLaplacianInverse_spec (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (ell : H1Zero g.leviCivitaData univ →L[ℝ] ℝ)
    (v : H1Zero g.leviCivitaData univ) :
    closedConformalLaplacianForm g (closedConformalLaplacianInverse g hY ell) v = ell v := by
  rw [closedConformalLaplacianForm_apply, closedConformalLaplacianInverse_apply,
    closedYamabeInverse_spec]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem closedConformalLaplacianInverse_unique (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (ell : H1Zero g.leviCivitaData univ →L[ℝ] ℝ)
    (w : H1Zero g.leviCivitaData univ)
    (hw : ∀ v, closedConformalLaplacianForm g w v = ell v) :
    w = closedConformalLaplacianInverse g hY ell := by
  rw [closedConformalLaplacianInverse_apply]
  apply closedYamabeInverse_unique g hY ((8 : ℝ) • ell) w
  intro v
  have h := hw v
  rw [closedConformalLaplacianForm_apply] at h
  simp only [smul_apply, smul_eq_mul]
  linarith

#print axioms closedYamabeForm_coe
#print axioms volume_pos_of_yamabe_pos
#print axioms closedYamabeForm_test_L2_lower
#print axioms closedYamabeForm_isCoercive
#print axioms closedYamabeInverse_spec
#print axioms existsUnique_closedYamabe_weakSolution
#print axioms closedConformalLaplacianForm_coe
#print axioms closedConformalLaplacianInverse_spec
#print axioms closedConformalLaplacianInverse_unique

end Yamabe3.Analysis
