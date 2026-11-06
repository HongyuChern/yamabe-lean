import Yamabe3.Analysis.DelaunayKernelThreshold
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Actual common-weight-two kernel bound from one true period

A central interval of one period has exactly the true period mass at every
convolution center. Its contribution is bounded by the genuine threshold
inequality. The complement is bounded directly by the integrable exponential
tails and 0<=v^4<=1, with no infinite period packet rearrangement.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

theorem futureWeightTwoKernel_integrable : Integrable futureWeightTwoKernel := by
  have h := ((spectralMajorant_integral (k₀ := (5 / 2 : ℝ)) (δ := (-2 : ℝ))
    (by norm_num) (by norm_num)).1).mul_const 5
  convert h using 1
  funext s
  rw [futureWeightTwoKernel_majorant]
  ring

theorem futureWeightTwoKernel_nonneg (s : ℝ) : 0 ≤ futureWeightTwoKernel s :=
  (Real.exp_pos _).le

theorem futureWeightTwoKernel_tail {R : ℝ} (hR : 0 ≤ R) :
    (∫ s in (Ioc (-R) R)ᶜ, futureWeightTwoKernel s) ≤
      (20 / 9) * Real.exp (-R / 2) := by
  have hi := futureWeightTwoKernel_integrable
  rw [compl_Ioc, setIntegral_union (Iic_disjoint_Ioi (by linarith)) measurableSet_Ioi
    (hi.restrict (s := _)) (hi.restrict (s := _))]
  have hL : (∫ s in Iic (-R), futureWeightTwoKernel s) =
      Real.exp (-(9 / 2) * R) / (9 / 2) := by
    calc
      _ = ∫ s in Iic (-R), Real.exp ((9 / 2) * s) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro s hs
        exact futureWeightTwoKernel_left ((show s ≤ -R from hs).trans (by linarith))
      _ = _ := by rw [integral_exp_mul_Iic (by norm_num)]; congr 2 <;> ring
  have hRi : (∫ s in Ioi R, futureWeightTwoKernel s) =
      -Real.exp (-(1 / 2) * R) / (-(1 / 2)) := by
    calc
      _ = ∫ s in Ioi R, Real.exp (-(1 / 2) * s) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro s hs
        exact futureWeightTwoKernel_right (hR.trans (show R < s from hs).le)
      _ = _ := integral_exp_mul_Ioi (by norm_num) R
  rw [hL, hRi]
  have he : Real.exp (-(9 / 2) * R) ≤ Real.exp (-R / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have heq : Real.exp (-(1 / 2) * R) = Real.exp (-R / 2) := by congr 1; ring
  rw [heq]
  nlinarith

/-- The true bounded density is integrated before it is estimated; the
central mass is therefore retained rather than replaced by a pointwise
supremum. -/
theorem weightTwo_full_mass_bound {p : ℝ → ℝ} (hp : Continuous p)
    (hb : ∀ s, 0 ≤ p s ∧ p s ≤ 1) {T : ℝ} (hT : 0 ≤ T) :
    (3 / 4) * (∫ s : ℝ, futureWeightTwoKernel s * p s) ≤
      (5 / 3) * (1 - weightTwoThreshold) +
        (3 / 4) * weightTwoThreshold * ((∫ s in Icc (-T / 2) (T / 2), p s) - 2) +
        (5 / 3) * Real.exp (-T / 4) := by
  have hi : Integrable (fun s => futureWeightTwoKernel s * p s) := by
    apply futureWeightTwoKernel_integrable.mono'
      (futureWeightTwoKernel_continuous.mul hp).aestronglyMeasurable
    exact Eventually.of_forall fun s => by
      change ‖futureWeightTwoKernel s * p s‖ ≤ futureWeightTwoKernel s
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (futureWeightTwoKernel_nonneg s) (hb s).1)]
      exact mul_le_of_le_one_right (futureWeightTwoKernel_nonneg s) (hb s).2
  have hcentral := weightTwo_central_mass_bound hp hb (-T / 2) (T / 2)
  simp only [integral_Icc_eq_integral_Ioc] at hcentral
  have htaille := integral_mono
    (hi.restrict (s := (Ioc (-T / 2) (T / 2))ᶜ))
    (futureWeightTwoKernel_integrable.restrict (s := (Ioc (-T / 2) (T / 2))ᶜ))
    (fun s => mul_le_of_le_one_right (futureWeightTwoKernel_nonneg s) (hb s).2)
  have htail := futureWeightTwoKernel_tail (R := T / 2) (by linarith)
  have he : -(T / 2) = -T / 2 := by ring
  have he' : -T / 2 / 2 = -T / 4 := by ring
  rw [he, he'] at htail
  rw [← integral_add_compl (s := Ioc (-T / 2) (T / 2)) measurableSet_Ioc hi]
  rw [integral_Icc_eq_integral_Ioc]
  linarith

/-- Actual conservation of a period integral at every translated and
reflected convolution center. -/
theorem periodic_central_mass {p : ℝ → ℝ} {T : ℝ}
    (hp : Function.Periodic p T) (hT : 0 ≤ T) (t : ℝ) :
    (∫ s in Icc (-T / 2) (T / 2), p (t - s)) = ∫ s in (0 : ℝ)..T, p s := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -T / 2 ≤ T / 2),
    intervalIntegral.integral_comp_sub_left]
  have he : t - (-T / 2) = (t - T / 2) + T := by ring
  rw [he, hp.intervalIntegral_add_eq (t - T / 2) 0, zero_add]

/-- The actual high-mode diagonal majorant against the actual Delaunay
potential at decay weight two. The estimate uses its true time mass and
period, and is uniform in the convolution center. -/
theorem weightTwo_periodic_potential_bound {v : ℝ → ℝ} (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    (hp : Function.Periodic v T) (t : ℝ) :
    (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * ((15 / 4) * v (t - s) ^ 4)) ≤
      (5 / 3) * (1 - weightTwoThreshold) +
        (3 / 4) * weightTwoThreshold * ((∫ s in (0 : ℝ)..T, v s ^ 4) - 2) +
        (5 / 3) * Real.exp (-T / 4) := by
  have hb4 (s : ℝ) : 0 ≤ v (t - s) ^ 4 ∧ v (t - s) ^ 4 ≤ 1 :=
    ⟨pow_nonneg (hb _).1 4, pow_le_one₀ (hb _).1 (hb _).2⟩
  have h := weightTwo_full_mass_bound
    ((hv.comp (continuous_const.sub continuous_id)).pow 4) hb4 hT
  simp only [Pi.pow_apply, Function.comp_apply, Pi.sub_apply, id_eq] at h
  have hp4 : Function.Periodic (fun s => v s ^ 4) T := hp.comp (fun z => z ^ 4)
  rw [periodic_central_mass hp4 hT t] at h
  have hfun : (fun s : ℝ => spectralMajorant (5 / 2) (-2) s * ((15 / 4) * v (t - s) ^ 4)) =
      fun s : ℝ => (3 / 4) * (futureWeightTwoKernel s * v (t - s) ^ 4) := by
    funext s
    rw [futureWeightTwoKernel_majorant]
    ring
  rw [hfun, integral_const_mul]
  exact h

end Yamabe3.Analysis.Delaunay
