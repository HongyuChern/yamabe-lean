import Yamabe3.Analysis.CriticalSourceDilation
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The true three-dimensional exterior inverse-fourth-power tail is
in L^(3/2). Its critical norm decays as radius^(-2). This is an exterior
tail estimate, not smallness of the whole bubble potential. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)

private theorem exterior_rpow_integrable {α : ℝ} (hα : 3 < α) :
    Integrable (fun x : E => (Ioi (1 : ℝ)).indicator (fun r : ℝ => r ^ (-α)) ‖x‖) volume := by
  rw [integrable_fun_norm_addHaar volume]
  have hi : IntegrableOn (fun r : ℝ => r ^ (2-α)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hj := hi.integrable_indicator measurableSet_Ioi
  apply (hj.mono_measure Measure.restrict_le_self).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  by_cases h : 1 < r
  · simp only [indicator, mem_Ioi, if_pos h, finrank_euclideanSpace, Fintype.card_fin,
      Nat.reduceSub, smul_eq_mul]
    rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr]
    congr 1
  · simp [h]

def exteriorInverseFourth (R : ℝ) (x : E) : ℝ :=
  (Ioi R).indicator (fun r : ℝ => r ^ (-4 : ℝ)) ‖x‖

theorem exteriorInverseFourth_memLp_one :
    MemLp (exteriorInverseFourth 1) (3/2 : ℝ≥0∞) volume := by
  have hm : AEStronglyMeasurable (exteriorInverseFourth 1) volume := by
    exact (((measurable_id.pow measurable_const).indicator measurableSet_Ioi).comp
      (continuous_norm.measurable : Measurable (fun x : E => ‖x‖))).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hm (by norm_num) (by finiteness)).mp
  apply (exterior_rpow_integrable (α := 6) (by norm_num)).congr
  filter_upwards with x
  by_cases hx : 1 < ‖x‖
  · simp only [exteriorInverseFourth, indicator, mem_Ioi, if_pos hx]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  · simp [exteriorInverseFourth, hx]

theorem exteriorInverseFourth_exp_dilation (s : ℝ) (x : E) :
    exteriorInverseFourth (Real.exp s) x =
      Real.exp (-4*s) * exteriorInverseFourth 1 (Real.exp (-s) • x) := by
  have hnorm : ‖Real.exp (-s) • x‖ = Real.exp (-s)*‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hcut : 1 < Real.exp (-s)*‖x‖ ↔ Real.exp s < ‖x‖ := by
    rw [← div_lt_iff₀' (Real.exp_pos (-s))]
    simp [one_div, ← Real.exp_neg]
  by_cases hx : Real.exp s < ‖x‖
  · have hpos : 0 < ‖x‖ := (Real.exp_pos s).trans hx
    simp only [exteriorInverseFourth, indicator, mem_Ioi, if_pos hx, hnorm,
      if_pos (hcut.mpr hx)]
    rw [Real.mul_rpow (Real.exp_pos _).le (norm_nonneg _), ← Real.exp_mul,
      ← mul_assoc, ← Real.exp_add]
    have he : -4*s+(-s)*(-4)=0 := by ring
    rw [he, Real.exp_zero, one_mul]
  · simp [exteriorInverseFourth, hx, hnorm, hcut]

theorem exteriorInverseFourth_critical_norm (s : ℝ) :
    eLpNorm (exteriorInverseFourth (Real.exp s)) (3/2 : ℝ≥0∞) volume =
      ENNReal.ofReal (Real.exp (-2*s)) * eLpNorm (exteriorInverseFourth 1) (3/2 : ℝ≥0∞) volume := by
  have heq := funext (exteriorInverseFourth_exp_dilation s)
  rw [heq]
  change eLpNorm (Real.exp (-4*s) • (fun x : E => exteriorInverseFourth 1 (Real.exp (-s) • x))) _ _ = _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (Real.exp_pos _).le]
  have hmap : MeasurableEmbedding (fun x : E => Real.exp (-s) • x) :=
    (Homeomorph.smulOfNeZero (Real.exp (-s)) (Real.exp_pos _).ne' : E ≃ₜ E).measurableEmbedding
  have hd : eLpNorm (fun x : E => exteriorInverseFourth 1 (Real.exp (-s) • x)) (3/2 : ℝ≥0∞) volume =
      (ENNReal.ofReal |(Real.exp (-s)^3)⁻¹|)^((1/(3/2 : ℝ≥0∞)).toReal) *
        eLpNorm (exteriorInverseFourth 1) (3/2 : ℝ≥0∞) volume := by
    change eLpNorm ((exteriorInverseFourth 1) ∘ (fun x : E => Real.exp (-s) • x)) _ _ = _
    rw [← hmap.eLpNorm_map_measure, Measure.map_addHaar_smul volume (Real.exp_pos (-s)).ne',
      eLpNorm_smul_measure_of_ne_zero (by positivity)]
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  rw [hd]
  have hfac : |(Real.exp (-s)^3)⁻¹| = Real.exp (3*s) := by
    rw [abs_of_pos (inv_pos.mpr (pow_pos (Real.exp_pos _) _)), ← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    ring
  rw [hfac]
  norm_num only [show (1/(3/2 : ℝ≥0∞)).toReal = (2/3 : ℝ) by norm_num]
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
    ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

theorem exteriorInverseFourth_memLp_exp (s : ℝ) :
    MemLp (exteriorInverseFourth (Real.exp s)) (3/2 : ℝ≥0∞) volume := by
  have hm : MemLp (fun x : E => exteriorInverseFourth 1 (Real.exp (-s) • x)) (3/2 : ℝ≥0∞) volume := by
    simpa only [preimage_univ, Measure.restrict_univ] using
      (memLp_comp_dilation (Real.exp_pos (-s)).ne' (O := univ)
        (by simpa only [Measure.restrict_univ] using exteriorInverseFourth_memLp_one))
  exact (hm.const_mul (Real.exp (-4*s))).ae_eq
    (Filter.Eventually.of_forall fun x => (exteriorInverseFourth_exp_dilation s x).symm)

#print axioms exteriorInverseFourth_memLp_one
#print axioms exteriorInverseFourth_exp_dilation
#print axioms exteriorInverseFourth_critical_norm
#print axioms exteriorInverseFourth_memLp_exp
end Yamabe3.Analysis.UniformElliptic
