import Yamabe3.Analysis.YamabeCoercivity

/-!
# Critical smallness of the actual quartic Yamabe potential

The small quantity is the native L6 integral of the actual background
function. Hölder and the genuine Yamabe inequality control its quartic
potential by the retained energy, then completion density transports
the estimate to the native H1 space. No spectral gap or inverse is an
extra field. Uniformity is in every smooth background satisfying the
displayed quantitative smallness condition.
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

theorem native_quartic_holder (g : RiemannianMetric 3 M)
    (u : M → ℝ) (hu : Continuous u)
    (f : EnergyTest g.leviCivitaData univ) :
    (∫ x, u x ^ 4 * f x * f x ∂g.volumeMeasure) ≤
      (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) *
        (∫ x, |f x| ^ 6 ∂g.volumeMeasure) ^ (1 / 3 : ℝ) := by
  have hpq : (3 / 2 : ℝ).HolderConjugate 3 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hu4 : MemLp (fun x => |u x| ^ 4) (ENNReal.ofReal (3 / 2 : ℝ)) g.volumeMeasure :=
    (hu.abs.pow 4).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hf2 : MemLp (fun x => |f x| ^ 2) (ENNReal.ofReal (3 : ℝ)) g.volumeMeasure :=
    (f.smooth.continuous.abs.pow 2).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp4 (x : ℝ) : (|x| ^ 4) ^ (3 / 2 : ℝ) = |x| ^ 6 := by
    rw [← Real.rpow_natCast_mul (abs_nonneg x)]
    norm_num [Real.rpow_natCast]
  have hp2 (x : ℝ) : (|x| ^ 2) ^ (3 : ℝ) = |x| ^ 6 := by
    rw [Real.rpow_ofNat, ← pow_mul]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun x => pow_nonneg (abs_nonneg (u x)) 4)
    (Filter.Eventually.of_forall fun x => sq_nonneg |f x|) hu4 hf2
  have hleft : (∫ x, |u x| ^ 4 * |f x| ^ 2 ∂g.volumeMeasure) =
      ∫ x, u x ^ 4 * f x * f x ∂g.volumeMeasure := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change |u x| ^ 4 * |f x| ^ 2 = u x ^ 4 * f x * f x
      rw [(by decide : Even 4).pow_abs, sq_abs]
      ring
  simpa only [hp4, hp2, hleft, show (1 / (3 / 2) : ℝ) = 2 / 3 by norm_num] using h

/-- The actual native linearization of `-8 Δ u + R u - 6 u^5`,
as a continuous bilinear form on the retained energy completion. -/
def closedYamabeJacobianForm (g : RiemannianMetric 3 M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u) :
    H1Zero g.leviCivitaData univ →L[ℝ] H1Zero g.leviCivitaData univ →L[ℝ] ℝ :=
  closedYamabeForm g - (30 : ℝ) • potentialForm g.leviCivitaData univ
    (by simpa using isCompact_univ) (fun x => u x ^ 4) (hu.pow 4)

theorem closedYamabeJacobianForm_apply (g : RiemannianMetric 3 M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (v w : H1Zero g.leviCivitaData univ) :
    closedYamabeJacobianForm g u hu v w = closedYamabeForm g v w -
      30 * potentialForm g.leviCivitaData univ (by simpa using isCompact_univ)
        (fun x => u x ^ 4) (hu.pow 4) v w := rfl

theorem closedYamabeJacobianForm_coe (g : RiemannianMetric 3 M)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (f h : EnergyTest g.leviCivitaData univ) :
    closedYamabeJacobianForm g u hu (f : H1Zero g.leviCivitaData univ)
      (h : H1Zero g.leviCivitaData univ) =
    ∫ x, (8 * g.inner x (g.leviCivitaData.gradient f x)
          (g.leviCivitaData.gradient h x) +
      (g.leviCivitaData.scalarCurvature x - 30 * u x ^ 4) * f x * h x) ∂g.volumeMeasure := by
  rw [closedYamabeJacobianForm_apply, potentialForm_coe]
  unfold closedYamabeForm
  rw [schrodingerForm_coe, ← integral_const_mul]
  have hi : Integrable (fun x => 8 * g.inner x (g.leviCivitaData.gradient f x)
      (g.leviCivitaData.gradient h x) + g.leviCivitaData.scalarCurvature x * f x * h x)
      g.volumeMeasure :=
    ((f.integrable_gradient h).const_mul 8).add
      (by simpa only [EnergyTest.mulSmooth_apply] using
        (f.mulSmooth g.leviCivitaData.scalarCurvature
          g.leviCivitaData.contMDiff_scalarCurvature).integrable_mul h)
  have hj : Integrable (fun x => 30 * (u x ^ 4 * f x * h x)) g.volumeMeasure := by
    simpa only [EnergyTest.mulSmooth_apply] using
      ((f.mulSmooth (fun x => u x ^ 4) (hu.pow 4)).integrable_mul h).const_mul 30
  rw [← integral_sub hi hj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

theorem closedYamabeJacobianForm_half_energy (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hsmall : 60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤
      Target.yamabeConstant g)
    (w : H1Zero g.leviCivitaData univ) :
    (1 / 2 : ℝ) * closedYamabeForm g w w ≤ closedYamabeJacobianForm g u hu w w := by
  induction w using Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih f =>
    by_cases hz : (f : M → ℝ) = 0
    · have hf : f = 0 := Subtype.ext hz
      rw [hf, Completion.coe_zero]
      simp
    · rw [closedYamabeJacobianForm_apply, potentialForm_coe, closedYamabeForm_coe]
      have hholder := native_quartic_holder g u hu.continuous f
      have henergy := Target.energy_lower_bound g hY f.smooth hz
      have hden : 0 ≤ (∫ x, |f x| ^ 6 ∂g.volumeMeasure) ^ (1 / 3 : ℝ) :=
        Real.rpow_nonneg (integral_nonneg fun x => pow_nonneg (abs_nonneg (f x)) 6) _
      have hsmall' := mul_le_mul_of_nonneg_right hsmall hden
      linarith only [hholder, henergy, hsmall']

/-- A single positive coercivity constant is chosen before all actual
small backgrounds. The true positive Yamabe constant supplies it. -/
theorem exists_uniform_closedYamabeJacobian_coercivity (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (u : M → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u),
      60 * (∫ x, |u x| ^ 6 ∂g.volumeMeasure) ^ (2 / 3 : ℝ) ≤ Target.yamabeConstant g →
      ∀ w : H1Zero g.leviCivitaData univ,
        κ * ‖w‖ ^ 2 ≤ closedYamabeJacobianForm g u hu w w := by
  obtain ⟨κ, hκ, hcoer⟩ := closedYamabeForm_isCoercive g hY
  refine ⟨κ / 2, half_pos hκ, fun u hu hsmall w => ?_⟩
  have hbase := hcoer w
  have hhalf := closedYamabeJacobianForm_half_energy g hY u hu hsmall w
  nlinarith only [hbase, hhalf]

#print axioms native_quartic_holder
#print axioms closedYamabeJacobianForm_coe
#print axioms closedYamabeJacobianForm_half_energy
#print axioms exists_uniform_closedYamabeJacobian_coercivity

end Yamabe3.Analysis
