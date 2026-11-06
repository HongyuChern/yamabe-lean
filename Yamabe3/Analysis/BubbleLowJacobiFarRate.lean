import Yamabe3.Analysis.BubbleLowPastSolver

/-! Quantitative negative-time decay of the actual regular bubble
Jacobi functions, retaining the slow radial rate exp(t/2). -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

private theorem power_bound (a t : ℝ) :
    |bubbleExpPower a (-3/2) t| ≤ Real.exp (a*t) := by
  dsimp only [bubbleExpPower]
  rw [abs_mul,abs_of_pos (Real.exp_pos _),abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.exp_pos (2*t)] : (1 : ℝ) ≤ 1+Real.exp (2*t)) (by norm_num : (-3/2 : ℝ) ≤ 0))
    (Real.exp_pos (a*t)).le

private theorem slope_bound (a t : ℝ) :
    |bubbleLogSlope a (-3/2) t| ≤ |a|+3 := by
  have he : 0 < Real.exp (2*t) := Real.exp_pos _
  have hd : 0 < 1+Real.exp (2*t) := by positivity
  have hh : 3*Real.exp (2*t)/(1+Real.exp (2*t)) ≤ 3 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hid : bubbleLogSlope a (-3/2) t = a-3*Real.exp (2*t)/(1+Real.exp (2*t)) := by
    dsimp only [bubbleLogSlope]
    ring
  rw [hid]
  exact (abs_sub _ _).trans (add_le_add le_rfl (by rw [abs_of_nonneg (by positivity)];exact hh))

theorem bubbleLowJacobi_value_far_rate (i : AngularIndex) (t : ℝ) (ht : t ≤ 0) :
    |bubbleLowJacobi i t| ≤ Real.exp (t/2) := by
  have he : Real.exp (2*t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold bubbleLowJacobi
  split_ifs
  · dsimp only [bubbleLowRadial]
    rw [abs_mul]
    have hb : |1-Real.exp (2*t)| ≤ 1 := abs_le.mpr ⟨by linarith [Real.exp_pos (2*t)],by linarith [Real.exp_pos (2*t)]⟩
    exact (mul_le_mul (power_bound (1/2) t) hb (abs_nonneg _) (Real.exp_pos _).le).trans_eq (by rw [mul_one]; congr 1; ring)
  · change |bubbleExpPower (3/2) (-3/2) t| ≤ _
    exact (power_bound (3/2) t).trans (Real.exp_le_exp.mpr (by linarith))

theorem bubbleLowJacobi_derivatives_far_rate (i : AngularIndex) (hi : i∈nativeLowIndexFinset)
    (t : ℝ) (ht : t ≤ 0) :
    |deriv (bubbleLowJacobi i) t| ≤ 8*Real.exp (t/2) ∧
      |deriv (deriv (bubbleLowJacobi i)) t| ≤ 8*Real.exp (t/2) := by
  have hvalue := bubbleLowJacobi_value_far_rate i t ht
  constructor
  · have he : Real.exp (2*t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have he0 := (Real.exp_pos (2*t)).le
    have hb : |1-Real.exp (2*t)| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
    have ht0 : 0 ≤ Real.exp (t/2) := (Real.exp_pos _).le
    unfold bubbleLowJacobi
    split_ifs
    · rw [show deriv bubbleLowRadial t =
        bubbleExpPower (1/2) (-3/2) t*bubbleLogSlope (1/2) (-3/2) t*(1-Real.exp (2*t))-
          2*bubbleExpPower (1/2) (-3/2) t*Real.exp (2*t) from (bubbleLowRadial_hasDerivAt t).deriv]
      have hB : |bubbleExpPower (1/2) (-3/2) t| ≤ Real.exp (t/2) := by convert! power_bound (1/2) t using 1 <;> congr 1 <;> ring
      have hS : |bubbleLogSlope (1/2) (-3/2) t| ≤ 7/2 := by have h := slope_bound (1/2) t; norm_num at h ⊢; exact h
      have h1 : |bubbleExpPower (1/2) (-3/2) t*bubbleLogSlope (1/2) (-3/2) t*(1-Real.exp (2*t))| ≤ Real.exp (t/2)*(7/2) := by
        rw [abs_mul,abs_mul]
        exact (mul_le_mul (mul_le_mul hB hS (abs_nonneg _) ht0) hb (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
      have h2 : |2*bubbleExpPower (1/2) (-3/2) t*Real.exp (2*t)| ≤ 2*Real.exp (t/2) := by
        rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2),abs_of_nonneg he0]
        exact (mul_le_mul (mul_le_mul_of_nonneg_left hB (by norm_num)) he he0 (by positivity)).trans_eq (mul_one _)
      exact ((abs_sub _ _).trans (add_le_add h1 h2)).trans (by nlinarith)
    · change |deriv (bubbleExpPower (3/2) (-3/2)) t| ≤ _
      rw [(bubbleExpPower_hasDerivAt (3/2) (-3/2) t).deriv,abs_mul]
      have hB := (power_bound (3/2) t).trans (Real.exp_le_exp.mpr (by linarith : (3/2)*t ≤ t/2))
      have hS : |bubbleLogSlope (3/2) (-3/2) t| ≤ 9/2 := by have h := slope_bound (3/2) t; norm_num at h ⊢; exact h
      exact (mul_le_mul hB hS (abs_nonneg _) ht0).trans (by nlinarith)
  · have hid : deriv (deriv (bubbleLowJacobi i)) t = bubbleLowCoefficient i t*bubbleLowJacobi i t := by
      have hh := bubbleLowJacobi_equation i hi t
      dsimp only [bubbleLowCoefficient]
      linarith
    rw [hid,abs_mul]
    exact (mul_le_mul (bubbleLowCoefficient_bound i hi t) hvalue (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 7/2)).trans (by nlinarith [Real.exp_pos (t/2)])

#print axioms bubbleLowJacobi_value_far_rate
#print axioms bubbleLowJacobi_derivatives_far_rate
end Yamabe3.Analysis.Delaunay
