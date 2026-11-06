import Yamabe3.Analysis.Green.RegularizedNewton
import Yamabe3.Analysis.Green.EuclideanResidual

/-! Uniform integrable domination for the density part of a regularized
Newton parametrix. This is an analytic estimate; native operator identification
is proved separately in NativeRegularization. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal

namespace Yamabe3.Analysis.GreenParametrix

open Yamabe3.RegularizedNewton

def regularizedDensityResidual (ρ V : E → ℝ) (ε : ℝ) (x : E) : ℝ :=
  (fderiv ℝ ρ x x / ρ x) * (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) +
    V x * potential ε x

theorem regularizedDensityResidual_bound {ρ V : E → ℝ} {c C B : ℝ}
    (ε : ℝ) {x : E}
    (hc : 0 < c) (hC : 0 ≤ C) (hρ : c ≤ ρ x)
    (hD : ‖fderiv ℝ ρ x‖ ≤ C * ‖x‖) (hV : |V x| ≤ B)
    (hx : x ≠ 0) :
    |regularizedDensityResidual ρ V ε x| ≤ (C / c + B) * ‖x‖⁻¹ := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hρpos : 0 < ρ x := hc.trans_le hρ
  have hnum : |fderiv ℝ ρ x x| ≤ C * ‖x‖ ^ 2 := by
    calc
      _ = ‖fderiv ℝ ρ x x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ ρ x‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (C * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right hD hr.le
      _ = _ := by ring
  have hp3 : 0 ≤ (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) := by positivity
  have hp3bound : (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) ≤ (‖x‖ ^ 3)⁻¹ := by
    simpa using radial_rpow_le_inv_pow ε hr 3
  have hp0 := potential_nonneg ε x
  have hB : 0 ≤ B := (abs_nonneg (V x)).trans hV
  have hpotbound := potential_le_inv_norm ε hx
  unfold regularizedDensityResidual
  calc
    _ ≤ |(fderiv ℝ ρ x x / ρ x) * (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ))| +
      |V x * potential ε x| := abs_add_le _ _
    _ = (|fderiv ℝ ρ x x| / ρ x) * (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) +
      |V x| * potential ε x := by
        rw [abs_mul, abs_div, abs_of_pos hρpos, abs_of_nonneg hp3,
          abs_mul, abs_of_nonneg (potential_nonneg ε x)]
    _ ≤ (C * ‖x‖ ^ 2 / c) * (‖x‖ ^ 3)⁻¹ + B * ‖x‖⁻¹ := by
      gcongr
    _ = _ := by field_simp

theorem tendsto_regularizedDensityResidual {ρ V : E → ℝ} {x : E}
    (hx : x ≠ 0) :
    Tendsto (fun ε : ℝ => regularizedDensityResidual ρ V ε x) (𝓝 0)
      (𝓝 (densityResidual ρ V x)) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hbase : Tendsto (fun ε : ℝ => ‖x‖ ^ 2 + ε ^ 2) (𝓝 0)
      (𝓝 (‖x‖ ^ 2)) := by
    have hc : Continuous (fun ε : ℝ => ‖x‖ ^ 2 + ε ^ 2) := by fun_prop
    simpa using hc.tendsto (0 : ℝ)
  have hp := hbase.rpow_const (p := -(3 / 2 : ℝ))
    (Or.inl (sq_pos_of_pos hr).ne')
  have hpval : (‖x‖ ^ 2) ^ (-(3 / 2 : ℝ)) = (‖x‖ ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast_mul hr.le 2 (-(3 / 2 : ℝ))]
    norm_num [Real.rpow_neg hr.le]
  rw [hpval] at hp
  have ht := (hp.const_mul (fderiv ℝ ρ x x / ρ x)).add
    ((tendsto_potential hx).const_mul (V x))
  convert ht using 1
  · rfl
  · congr 1
    unfold densityResidual
    field_simp

/-- The regularized density error may be passed through an actual local
Lebesgue integral. A coordinate volume density can be included in `ψ`. -/
theorem tendsto_integral_regularizedDensityResidual {ρ V ψ : E → ℝ}
    {R c C B M : ℝ} (hρsmooth : ContDiff ℝ ∞ ρ)
    (hVmeas : Measurable V) (hψmeas : Measurable ψ)
    (hc : 0 < c) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hρ : ∀ x ∈ ball (0 : E) R, c ≤ ρ x)
    (hD : ∀ x ∈ ball (0 : E) R, ‖fderiv ℝ ρ x‖ ≤ C * ‖x‖)
    (hV : ∀ x ∈ ball (0 : E) R, |V x| ≤ B)
    (hψ : ∀ x ∈ ball (0 : E) R, |ψ x| ≤ M) :
    Tendsto (fun ε : ℝ => ∫ x in ball (0 : E) R,
      ψ x * regularizedDensityResidual ρ V ε x) (𝓝 0)
      (𝓝 (∫ x in ball (0 : E) R, ψ x * densityResidual ρ V x)) := by
  let : IsFiniteMeasure (volume.restrict (ball (0 : E) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hderiv : ContDiff ℝ ∞ (fderiv ℝ ρ) := hρsmooth.fderiv_right (by simp)
  have hm (ε : ℝ) : Measurable (regularizedDensityResidual ρ V ε) := by
    unfold regularizedDensityResidual potential
    exact ((((hderiv.continuous.clm_apply continuous_id).measurable.div
      hρsmooth.continuous.measurable).mul
      (((measurable_norm.pow_const 2).add measurable_const).pow_const (-(3 / 2 : ℝ)))).add
      (hVmeas.mul (((measurable_norm.pow_const 2).add measurable_const).pow_const
        (-(1 / 2 : ℝ)))))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x : E => (M * (C / c + B)) * ‖x‖⁻¹)
  · exact Eventually.of_forall (fun ε => (hψmeas.mul (hm ε)).aestronglyMeasurable)
  · apply Eventually.of_forall
    intro ε
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0 : E))] with x hx hx0
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ M * ((C / c + B) * ‖x‖⁻¹) :=
        mul_le_mul (hψ x hx)
          (regularizedDensityResidual_bound ε hc hC (hρ x hx) (hD x hx) (hV x hx) hx0)
          (abs_nonneg _) hM
      _ = _ := by ring
  · exact (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (memLp_inv_norm R)).const_mul _
  · filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : E))] with x hx0
    exact (tendsto_regularizedDensityResidual (ρ := ρ) (V := V) hx0).const_mul (ψ x)

#print axioms regularizedDensityResidual_bound
#print axioms tendsto_regularizedDensityResidual
#print axioms tendsto_integral_regularizedDensityResidual

end Yamabe3.Analysis.GreenParametrix
