import Yamabe3.Analysis.ExteriorPowerCriticalTail
import Yamabe3.Analysis.FullBubbleSpatialPotentialJets

/-! The actual full-bubble spatial potential, restricted outside a
large radius, has critical norm O(exp(-2s)). Hölder then controls its
reaction against the same L6 field. No global feedback inverse is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay

def fullBubblePotentialTail (τ R : ℝ) (x : E) : ℝ :=
  {y : E | R < ‖y‖}.indicator (fullBubbleSpatialPotential (Real.exp τ)) x

private theorem fullBubble_tail_bound (τ s : ℝ) (x : E) :
    ‖fullBubblePotentialTail τ (Real.exp s) x‖ ≤
      (15*Real.exp (2*τ))*‖exteriorInverseFourth (Real.exp s) x‖ := by
  by_cases hx : Real.exp s < ‖x‖
  · have hp : 0 < ‖x‖ := (Real.exp_pos _).trans hx
    simp only [fullBubblePotentialTail, exteriorInverseFourth, indicator, mem_setOf_eq, mem_Ioi,
      if_pos hx, fullBubbleSpatialPotential]
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    have hden : ‖x‖^4 ≤ (‖x‖^2+Real.exp τ^2)^2 := by
      nlinarith only [sq_nonneg ‖x‖, sq_nonneg (Real.exp τ), mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg (Real.exp τ))]
    have hh := div_le_div_of_nonneg_left (by positivity : 0 ≤ 15*Real.exp τ^2) (pow_pos hp 4) hden
    have hid : (15*Real.exp τ^2)/‖x‖^4 = (15*Real.exp (2*τ))*(‖x‖^(-4 : ℝ)) := by
      rw [Real.rpow_neg (norm_nonneg _), Real.rpow_ofNat, ← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      ring
    exact hh.trans_eq hid
  · simp [fullBubblePotentialTail, exteriorInverseFourth, hx]

theorem fullBubblePotentialTail_memLp (τ s : ℝ) :
    MemLp (fullBubblePotentialTail τ (Real.exp s)) (3/2 : ℝ≥0∞) volume := by
  have hm : AEStronglyMeasurable (fullBubblePotentialTail τ (Real.exp s)) volume := by
    have hc' : Continuous (fullBubbleSpatialPotential (Real.exp τ)) := by
      exact continuous_const.div (((continuous_norm.pow 2).add continuous_const).pow 2) (fun x => by positivity)
    exact (hc'.measurable.indicator (measurableSet_lt measurable_const continuous_norm.measurable)).aestronglyMeasurable
  exact (exteriorInverseFourth_memLp_exp s).of_le_mul hm
    (Filter.Eventually.of_forall (fullBubble_tail_bound τ s))

theorem fullBubblePotentialTail_critical_norm (τ s : ℝ) :
    eLpNorm (fullBubblePotentialTail τ (Real.exp s)) (3/2 : ℝ≥0∞) volume ≤
      (ENNReal.ofReal (15*Real.exp (2*τ))*eLpNorm (exteriorInverseFourth 1) (3/2 : ℝ≥0∞) volume)*
        ENNReal.ofReal (Real.exp (-2*s)) := by
  have hh := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := volume)
    (Filter.Eventually.of_forall (fullBubble_tail_bound τ s)) (3/2 : ℝ≥0∞)
  rw [exteriorInverseFourth_critical_norm] at hh
  exact hh.trans_eq (by ring)

private instance tailHolder : ENNReal.HolderTriple (3/2) 6 (6/5) := by
  constructor
  have h32 : (3/2 : ℝ≥0∞) ≠ 0 := ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
  have h65 : (6/5 : ℝ≥0∞) ≠ 0 := ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.add_ne_top.mpr ⟨ENNReal.inv_ne_top.mpr h32, by norm_num⟩)
    (ENNReal.inv_ne_top.mpr h65)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]

theorem fullBubblePotentialTail_reaction_bound (τ s : ℝ) (u : E → ℝ)
    (hu : MemLp u 6 volume) :
    MemLp (fun x : E => fullBubblePotentialTail τ (Real.exp s) x*u x) (6/5 : ℝ≥0∞) volume ∧
      eLpNorm (fun x : E => fullBubblePotentialTail τ (Real.exp s) x*u x) (6/5 : ℝ≥0∞) volume ≤
        ((ENNReal.ofReal (15*Real.exp (2*τ))*eLpNorm (exteriorInverseFourth 1) (3/2 : ℝ≥0∞) volume)*
          ENNReal.ofReal (Real.exp (-2*s)))*eLpNorm u 6 volume := by
  have hq := fullBubblePotentialTail_memLp τ s
  refine ⟨hu.mul' hq, ?_⟩
  exact (eLpNorm_smul_le_mul_eLpNorm (p := (3/2 : ℝ≥0∞)) hu.1 hq.1).trans
    (mul_le_mul (fullBubblePotentialTail_critical_norm τ s) le_rfl zero_le zero_le)

#print axioms fullBubblePotentialTail_memLp
#print axioms fullBubblePotentialTail_critical_norm
#print axioms fullBubblePotentialTail_reaction_bound
end Yamabe3.Analysis.SpherePolar
