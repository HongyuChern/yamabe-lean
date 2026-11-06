import Yamabe3.Analysis.SpectralKernelIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.Exponential

/-!
# A genuine weighted-kernel threshold estimate at decay weight two

For the actual weight delta=-2 and lowest high rate 5/2, the unit exponential
majorant has rates 9/2 to the left and 1/2 to the right. A fixed threshold
exp(-9/10) has a superlevel interval of length exactly two. Integrating the
pointwise threshold inequality yields the affine mass bound required by
the small-neck contraction. No rearrangement theorem or kernel estimate
is supplied as an input.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

/-- Five times the actual diagonal norm majorant at future decay weight two. -/
def futureWeightTwoKernel (s : ℝ) : ℝ := Real.exp (2 * s - (5 / 2) * |s|)

def weightTwoThreshold : ℝ := Real.exp (-(9 / 10 : ℝ))

def weightTwoExcess (s : ℝ) : ℝ :=
  (Icc (-(1 / 5 : ℝ)) (9 / 5)).indicator
    (fun x => futureWeightTwoKernel x - weightTwoThreshold) s

theorem futureWeightTwoKernel_left {s : ℝ} (hs : s ≤ 0) :
    futureWeightTwoKernel s = Real.exp ((9 / 2) * s) := by
  unfold futureWeightTwoKernel
  rw [abs_of_nonpos hs]
  congr 1
  ring

theorem futureWeightTwoKernel_right {s : ℝ} (hs : 0 ≤ s) :
    futureWeightTwoKernel s = Real.exp (-(1 / 2) * s) := by
  unfold futureWeightTwoKernel
  rw [abs_of_nonneg hs]
  congr 1
  ring

theorem futureWeightTwoKernel_continuous : Continuous futureWeightTwoKernel := by
  unfold futureWeightTwoKernel
  fun_prop

theorem futureWeightTwoKernel_majorant (s : ℝ) :
    spectralMajorant (5 / 2) (-2) s = futureWeightTwoKernel s / 5 := by
  unfold spectralMajorant futureWeightTwoKernel
  norm_num

private theorem weightTwo_threshold_lower : (2 / 5 : ℝ) < weightTwoThreshold := by
  have h := Real.exp_bound' (x := (9 / 10 : ℝ)) (by norm_num) (by norm_num)
    (n := 4) (by decide)
  norm_num [Finset.sum_range_succ] at h
  have he : Real.exp (9 / 10 : ℝ) < 5 / 2 := by linarith
  unfold weightTwoThreshold
  rw [Real.exp_neg, inv_eq_one_div, lt_div_iff₀ (Real.exp_pos _)]
  nlinarith

theorem weightTwo_threshold_gap : (5 / 3 : ℝ) * (1 - weightTwoThreshold) < 1 := by
  have h := weightTwo_threshold_lower
  linarith

theorem weightTwoExcess_nonneg (s : ℝ) : 0 ≤ weightTwoExcess s := by
  by_cases hs : s ∈ Icc (-(1 / 5 : ℝ)) (9 / 5)
  · rw [weightTwoExcess, indicator_of_mem hs]
    apply sub_nonneg.mpr
    unfold weightTwoThreshold
    by_cases h0 : s ≤ 0
    · rw [futureWeightTwoKernel_left h0, Real.exp_le_exp]
      linarith [hs.1]
    · rw [futureWeightTwoKernel_right (le_of_not_ge h0), Real.exp_le_exp]
      linarith [hs.2]
  · simp only [weightTwoExcess, indicator_of_notMem hs, le_refl]

theorem weightTwo_threshold_pointwise {s p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    futureWeightTwoKernel s * p ≤ weightTwoThreshold * p + weightTwoExcess s := by
  by_cases hs : s ∈ Icc (-(1 / 5 : ℝ)) (9 / 5)
  · have hn := weightTwoExcess_nonneg s
    rw [weightTwoExcess, indicator_of_mem hs] at hn ⊢
    have hmul := mul_le_mul_of_nonneg_left hp1 hn
    nlinarith
  · rw [weightTwoExcess, indicator_of_notMem hs, add_zero]
    apply mul_le_mul_of_nonneg_right _ hp0
    unfold weightTwoThreshold
    have hd : s < -(1 / 5 : ℝ) ∨ (9 / 5 : ℝ) < s := by
      by_cases hl : s < -(1 / 5 : ℝ)
      · exact Or.inl hl
      · exact Or.inr (lt_of_not_ge fun hr => hs ⟨le_of_not_gt hl, hr⟩)
    rcases hd with hl | hr
    · rw [futureWeightTwoKernel_left (by linarith), Real.exp_le_exp]
      linarith
    · rw [futureWeightTwoKernel_right (by linarith), Real.exp_le_exp]
      linarith

private theorem integral_exp_multiple (c a b : ℝ) (hc : c ≠ 0) :
    (∫ x in a..b, Real.exp (c * x)) = (Real.exp (c * b) - Real.exp (c * a)) / c := by
  have hd (x : ℝ) : HasDerivAt (fun y => Real.exp (c * y) / c) (Real.exp (c * x)) x := by
    apply ((((hasDerivAt_id x).const_mul c).exp).div_const c).congr_deriv
    simp only [id_eq, mul_one]
    field_simp
  have hi : IntervalIntegrable (fun x : ℝ => Real.exp (c * x)) volume a b :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi
  rw [h]
  ring

theorem weightTwoExcess_integrable : Integrable weightTwoExcess := by
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  exact (futureWeightTwoKernel_continuous.sub continuous_const).integrableOn_Icc

/-- Exact integration of the actual positive excess over the fixed threshold. -/
theorem integral_weightTwoExcess :
    (∫ s : ℝ, weightTwoExcess s) = (20 / 9) * (1 - weightTwoThreshold) - 2 * weightTwoThreshold := by
  unfold weightTwoExcess
  rw [integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 5 : ℝ)) ≤ 9 / 5)]
  rw [intervalIntegral.integral_sub (futureWeightTwoKernel_continuous.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := (volume : Measure ℝ))
    (futureWeightTwoKernel_continuous.intervalIntegrable (-(1 / 5 : ℝ)) 0)
    (futureWeightTwoKernel_continuous.intervalIntegrable 0 (9 / 5))
  rw [← hsplit]
  have hL : (∫ s in (-(1 / 5 : ℝ))..0, futureWeightTwoKernel s) =
      ∫ s in (-(1 / 5 : ℝ))..0, Real.exp ((9 / 2) * s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (-(1 / 5 : ℝ)) 0 := by
      simpa only [uIcc_of_le (by norm_num : (-(1 / 5 : ℝ)) ≤ 0)] using hs
    exact futureWeightTwoKernel_left hs'.2
  have hR : (∫ s in (0 : ℝ)..9 / 5, futureWeightTwoKernel s) =
      ∫ s in (0 : ℝ)..9 / 5, Real.exp (-(1 / 2) * s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) (9 / 5) := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 9 / 5)] using hs
    exact futureWeightTwoKernel_right hs'.1
  rw [hL, hR, integral_exp_multiple _ _ _ (by norm_num),
    integral_exp_multiple _ _ _ (by norm_num)]
  norm_num [weightTwoThreshold]
  ring

/-- A bounded nonnegative density on an arbitrary finite interval is
controlled by its true interval mass and the integrated kernel excess. -/
theorem weightTwo_central_mass_bound {p : ℝ → ℝ} (hp : Continuous p)
    (hb : ∀ s, 0 ≤ p s ∧ p s ≤ 1) (a b : ℝ) :
    (∫ s in Icc a b, futureWeightTwoKernel s * p s) ≤
      weightTwoThreshold * (∫ s in Icc a b, p s) +
        (20 / 9) * (1 - weightTwoThreshold) - 2 * weightTwoThreshold := by
  have hkp : IntegrableOn (fun s => futureWeightTwoKernel s * p s) (Icc a b) :=
    (futureWeightTwoKernel_continuous.mul hp).integrableOn_Icc
  have hLambdaP : IntegrableOn (fun s => weightTwoThreshold * p s) (Icc a b) :=
    (continuous_const.mul hp).integrableOn_Icc
  have hq := weightTwoExcess_integrable.restrict (s := Icc a b)
  have h := integral_mono hkp (hLambdaP.add hq)
    (fun s => weightTwo_threshold_pointwise (hb s).1 (hb s).2)
  simp only [Pi.add_apply] at h
  rw [integral_add hLambdaP hq, integral_const_mul] at h
  have hQ := setIntegral_le_integral (s := Icc a b) weightTwoExcess_integrable
    (Eventually.of_forall weightTwoExcess_nonneg)
  rw [integral_weightTwoExcess] at hQ
  linarith

end Yamabe3.Analysis.Delaunay
