import Yamabe3.Analysis.DelaunayOval

/-!
# Actual smooth periodic Delaunay solutions in dimension three

This constructs the nonconstant periodic solution, normalized to have its
maximum at time zero, from an explicit smooth time integral and its proved
global inverse. Turning points, the second order ODE and the exact energy
level are all proved for the constructed function. No periodic-orbit or ODE
existence hypothesis is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

/-- The actual positive Delaunay orbit at every squared neck `a` below the
cylindrical threshold. Its period is the true time integral around the oval. -/
theorem exists_delaunay_periodic_squared {a : ℝ} (ha : 0 < a)
    (hsmall : 3 * a ^ 2 < 1) :
    ∃ (v : ℝ → ℝ) (T : ℝ),
      T = (∫ θ in Real.pi / 2..Real.pi / 2 + Real.pi,
        2 / Real.sqrt (ovalSquared a (upperSquared a) θ *
          (ovalSquared a (upperSquared a) θ + a + upperSquared a))) ∧
      0 < T ∧ ContDiff ℝ ∞ v ∧ Function.Periodic v T ∧
      (∀ t, Real.sqrt a ≤ v t ∧ v t ≤ Real.sqrt (upperSquared a)) ∧
      v 0 = Real.sqrt (upperSquared a) ∧ deriv v 0 = 0 ∧
      (∃ t, 0 < t ∧ t < T ∧ v t = Real.sqrt a) ∧
      (∀ t, deriv (deriv v) t = v t / 4 - 3 * v t ^ 5 / 4) ∧
      (∀ t, 4 * deriv v t ^ 2 + v t ^ 6 - v t ^ 2 = a ^ 3 - a) ∧
      (∀ t, 0 < v t ∧ v t < 1 ∧ |deriv v t| < v t / 2) ∧
      (∀ t, 0 < t → t < T → v t < v 0) ∧
      (∀ S, 0 < S → Function.Periodic v S → T ≤ S) := by
  let b := upperSquared a
  obtain ⟨hab, hb, hlevel⟩ := upperSquared_properties ha hsmall
  obtain ⟨θ, T, hTformula, hT, hθ, hmono, hθzero, hθderiv, hright, hleft, hshift⟩ :=
    exists_smooth_periodic_clock_inverse (ovalDensity_contDiff ha hab.le) Real.pi_pos
      (ovalDensity_periodic a b) (by norm_num : (0 : ℝ) < 1)
      (ovalDensity_ge_one ha hab.le hb.le) (Real.pi / 2)
  let v : ℝ → ℝ := fun t => ovalProfile a b (θ t)
  let z : ℝ → ℝ := fun t => ovalVelocity a b (θ t)
  have hθd (t : ℝ) : HasDerivAt θ (ovalSpeed a b (θ t)) t := by
    simpa only [ovalDensity, inv_inv] using hθderiv t
  have hvd (t : ℝ) : HasDerivAt v (z t) t := by
    have h := (ovalProfile_hasDerivAt ha hab.le (θ t)).comp t (hθd t)
    rw [ovalProfile_derivative_speed ha hab.le] at h
    exact h
  have hdv : deriv v = z := funext fun t => (hvd t).deriv
  have hzd (t : ℝ) : HasDerivAt z (v t / 4 - 3 * v t ^ 5 / 4) t := by
    have h := (ovalVelocity_hasDerivAt ha hab.le (θ t)).comp t (hθd t)
    rw [ovalVelocity_derivative_speed ha hab.le hlevel] at h
    exact h
  have hbounds (t : ℝ) : Real.sqrt a ≤ v t ∧ v t ≤ Real.sqrt b :=
    ovalProfile_bounds hab.le (θ t)
  have hzero : v 0 = Real.sqrt b := by
    simp only [v, hθzero, ovalProfile, ovalSquared, Real.sin_pi_div_two, one_pow, mul_one]
    congr 1
    ring
  have hz0 : deriv v 0 = 0 := by
    rw [hdv]
    simp only [z, hθzero, ovalVelocity, Real.cos_pi_div_two, mul_zero, zero_mul]
  have hθT : θ T = Real.pi / 2 + Real.pi := by simpa only [zero_add, hθzero] using hshift 0
  let τ : ℝ := timePrimitive (ovalDensity a b) (Real.pi / 2) Real.pi
  have hθτ : θ τ = Real.pi := hleft Real.pi
  have hτ0 : 0 < τ := by
    by_contra hn
    have h := hmono.monotone (le_of_not_gt hn)
    rw [hθτ, hθzero] at h
    linarith [Real.pi_pos]
  have hτT : τ < T := by
    by_contra hn
    have h := hmono.monotone (le_of_not_gt hn)
    rw [hθτ, hθT] at h
    linarith [Real.pi_pos]
  have hmin : v τ = Real.sqrt a := by
    simp only [v, hθτ, ovalProfile, ovalSquared, Real.sin_pi, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero]
  have henergy (t : ℝ) : 4 * deriv v t ^ 2 + v t ^ 6 - v t ^ 2 = a ^ 3 - a := by
    rw [hdv]
    exact oval_energy ha hab.le hlevel (θ t)
  have hpositive (t : ℝ) : 0 < v t := ovalProfile_pos ha hab.le (θ t)
  have hless (t : ℝ) : v t < 1 := by
    apply (hbounds t).2.trans_lt
    have h := Real.sqrt_lt_sqrt (ha.trans hab).le hb
    simpa only [Real.sqrt_one] using h
  have ha1 : a < 1 := hab.trans hb
  have hnegative : a ^ 3 - a < 0 := by
    have hs : a ^ 2 < 1 := by nlinarith
    nlinarith [mul_pos ha (sub_pos.mpr hs)]
  have hstrictMax (t : ℝ) (ht : 0 < t) (htT : t < T) : v t < v 0 := by
    have hθlower := hmono ht
    have hθupper := hmono htT
    rw [hθzero] at hθlower
    rw [hθT] at hθupper
    have hcos := Real.cos_neg_of_pi_div_two_lt_of_lt hθlower (by linarith : θ t < Real.pi + Real.pi / 2)
    rw [hzero]
    exact ovalProfile_lt_upper ha hab hcos.ne
  refine ⟨v, T, ?_, hT, (ovalProfile_contDiff ha hab.le).comp hθ, ?_,
    hbounds, hzero, hz0, ⟨τ, hτ0, hτT, hmin⟩, ?_, henergy, ?_, hstrictMax, ?_⟩
  · rw [hTformula]
    apply intervalIntegral.integral_congr
    intro s _
    exact ovalDensity_formula ha hab.le s
  · intro t
    change ovalProfile a b (θ (t + T)) = ovalProfile a b (θ t)
    rw [hshift]
    exact ovalProfile_periodic a b (θ t)
  · intro t
    rw [hdv]
    exact (hzd t).deriv
  · intro t
    refine ⟨hpositive t, hless t, ?_⟩
    have he := henergy t
    have hpow := pow_nonneg (hpositive t).le 6
    have habs := abs_nonneg (deriv v t)
    have hsq := sq_abs (deriv v t)
    nlinarith [hpositive t]
  · intro S hS hperiod
    by_contra hn
    have hlt := hstrictMax S hS (lt_of_not_ge hn)
    have heq : v S = v 0 := by simpa only [zero_add] using hperiod 0
    exact (ne_of_lt hlt) heq

/-- Neck-size version in the full nonconstant positive parameter range.
The energy constant is exactly `η^6−η²`; the construction does not confuse
neck size with the manuscript's separate small energy parameter. -/
theorem exists_delaunay_periodic {η : ℝ} (hη : 0 < η) (hsmall : 3 * η ^ 4 < 1) :
    ∃ (v : ℝ → ℝ) (T : ℝ),
      0 < T ∧ ContDiff ℝ ∞ v ∧ Function.Periodic v T ∧
      (∀ t, η ≤ v t ∧ v t ≤ Real.sqrt (upperSquared (η ^ 2))) ∧
      v 0 = Real.sqrt (upperSquared (η ^ 2)) ∧ deriv v 0 = 0 ∧
      (∃ t, 0 < t ∧ t < T ∧ v t = η) ∧
      (∀ t, deriv (deriv v) t = v t / 4 - 3 * v t ^ 5 / 4) ∧
      (∀ t, 4 * deriv v t ^ 2 + v t ^ 6 - v t ^ 2 = η ^ 6 - η ^ 2) ∧
      (∀ t, 0 < v t ∧ v t < 1 ∧ |deriv v t| < v t / 2) ∧
      (∀ t, 0 < t → t < T → v t < v 0) ∧
      (∀ S, 0 < S → Function.Periodic v S → T ≤ S) := by
  have ha : 0 < η ^ 2 := sq_pos_of_pos hη
  have hsmall' : 3 * (η ^ 2) ^ 2 < 1 := by nlinarith [hsmall]
  obtain ⟨v, T, _, hT, hs, hp, hb, h0, hd0, hmin, hode, he, hpos, hmax, hleast⟩ :=
    exists_delaunay_periodic_squared ha hsmall'
  refine ⟨v, T, hT, hs, hp, ?_, h0, hd0, ?_, hode, ?_, hpos, hmax, hleast⟩
  · simpa only [Real.sqrt_sq hη.le] using hb
  · simpa only [Real.sqrt_sq hη.le] using hmin
  · intro t
    convert he t using 1
    ring

#print axioms exists_delaunay_periodic_squared
#print axioms exists_delaunay_periodic

end Yamabe3.Analysis.Delaunay
