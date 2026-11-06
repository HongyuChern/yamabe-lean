import Yamabe3.Analysis.Green.RegularizedNewton
import Yamabe3.Analysis.Green.EuclideanResidual
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Actual L² membership of the cutoff Newton singularity, and the local
integral limit on the transposed side of the parametrix identity. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Yamabe3.Analysis.GreenParametrix

open Yamabe3.RegularizedNewton

theorem memLp_cutoff_inv_norm_withDensity (χ : ContDiffBump (0 : E))
    {ρ : E → ℝ} (hρ : Continuous ρ) :
    MemLp (fun x : E => χ x * ‖x‖⁻¹) 2
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) := by
  obtain ⟨A, hA⟩ := (isCompact_closedBall (0 : E) χ.rOut).exists_bound_of_continuousOn
    hρ.continuousOn
  have hlocal : MemLp (fun x : E => χ x * ‖x‖⁻¹) 2
      ((volume.restrict (ball (0 : E) χ.rOut)).withDensity
        (fun x => ENNReal.ofReal (ρ x))) := by
    apply memLp_withDensity_of_le_inv_norm (A := ENNReal.ofReal A) (C := 1)
      ENNReal.ofReal_ne_top
    · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      apply ENNReal.ofReal_le_ofReal
      exact (le_abs_self _).trans (hA x (ball_subset_closedBall hx))
    · exact (χ.continuous.measurable.mul measurable_norm.inv).aestronglyMeasurable
    · exact Eventually.of_forall (fun x => by
        rw [abs_mul, abs_of_nonneg χ.nonneg, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
        exact mul_le_mul_of_nonneg_right χ.le_one (inv_nonneg.mpr (norm_nonneg x)))
  rw [← restrict_withDensity measurableSet_ball] at hlocal
  have hi := (memLp_indicator_iff_restrict measurableSet_ball).mpr hlocal
  convert hi using 1
  ext x
  by_cases hx : x ∈ ball (0 : E) χ.rOut
  · simp [hx]
  · have hz : χ x = 0 := by
      apply Function.notMem_support.mp
      simpa only [χ.support_eq] using hx
    simp [hx, hz]

theorem tendsto_integral_potential_mul {ψ : E → ℝ} {R M : ℝ}
    (hm : Measurable ψ) (hM : 0 ≤ M)
    (hb : ∀ x ∈ ball (0 : E) R, |ψ x| ≤ M) :
    Tendsto (fun ε : ℝ => ∫ x in ball (0 : E) R, ψ x * potential ε x)
      (𝓝 0) (𝓝 (∫ x in ball (0 : E) R, ψ x * ‖x‖⁻¹)) := by
  let : IsFiniteMeasure (volume.restrict (ball (0 : E) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  apply tendsto_integral_filter_of_dominated_convergence (fun x : E => M * ‖x‖⁻¹)
  · apply Eventually.of_forall
    intro ε
    exact (hm.mul (((measurable_norm.pow_const 2).add measurable_const).pow_const
      (-(1 / 2 : ℝ)))).aestronglyMeasurable
  · apply Eventually.of_forall
    intro ε
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0 : E))] with x hx hx0
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (potential_nonneg ε x)]
    exact mul_le_mul (hb x hx) (potential_le_inv_norm ε hx0) (potential_nonneg ε x) hM
  · exact (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (memLp_inv_norm R)).const_mul M
  · filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : E))] with x hx0
    exact (tendsto_potential hx0).const_mul (ψ x)

#print axioms memLp_cutoff_inv_norm_withDensity
#print axioms tendsto_integral_potential_mul

end Yamabe3.Analysis.GreenParametrix
