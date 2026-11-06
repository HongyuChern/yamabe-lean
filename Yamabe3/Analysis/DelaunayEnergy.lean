import Yamabe3.Analysis.DelaunayPeriodic

/-!
# The manuscript's genuine energy parameters

The minimum is constructed from the actual cubic energy equation. This
connects the neck-parametrized periodic orbit to the two parameters ε,e,
without identifying ε with the exact minimum. The uniform lower bound needed
for end construction is derived from the actual energy equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

/-- An actual small negative energy determines a positive squared neck.
The cubic equation is solved by IVT, and the quantitative bounds are proved. -/
theorem exists_squared_neck_of_energy {q : ℝ} (hq : 0 < q) (hsmall : q < 3 / 8) :
    ∃ a : ℝ, 0 < a ∧ a < 1 / 2 ∧ a - a ^ 3 = q ∧ q ≤ a ∧ a ≤ 2 * q := by
  have hc : Continuous (fun a : ℝ => a - a ^ 3) := continuous_id.sub (continuous_id.pow 3)
  have hleft : (0 : ℝ) - 0 ^ 3 ≤ q := by simpa using hq.le
  have hright : q ≤ (1 / 2 : ℝ) - (1 / 2 : ℝ) ^ 3 := by norm_num; exact hsmall.le
  obtain ⟨a, ha, heq⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hc.continuousOn ⟨hleft, hright⟩
  have hap : 0 < a := by
    by_contra hn
    have haz : a = 0 := le_antisymm (le_of_not_gt hn) ha.1
    simp only [haz, zero_pow (by decide : 3 ≠ 0), sub_self] at heq
    linarith
  have hau : a < 1 / 2 := by
    by_contra hn
    have hae : a = 1 / 2 := le_antisymm ha.2 (le_of_not_gt hn)
    rw [hae] at heq
    norm_num at heq
    linarith
  have ha2 : a ^ 2 ≤ 1 / 4 := by nlinarith
  have ha3 : a ^ 3 ≤ a / 4 := by nlinarith [mul_nonneg hap.le (sub_nonneg.mpr ha2)]
  refine ⟨a, hap, hau, heq, ?_, ?_⟩
  · nlinarith [pow_nonneg hap.le 3]
  · linarith

/-- Actual periodic Delaunay solutions in the energy parameters used by the
manuscript. In particular the exact minimum is bounded below by ε sqrt(e),
and the conserved energy is exactly −ε²e. -/
theorem exists_delaunay_energy_parameters {ε e : ℝ}
    (hε : 0 < ε) (he : 0 < e) (hsmall : ε ^ 2 * e < 3 / 8) :
    ∃ (η : ℝ) (v : ℝ → ℝ) (T : ℝ),
      0 < η ∧ η ^ 2 * (1 - η ^ 4) = ε ^ 2 * e ∧
      ε * Real.sqrt e ≤ η ∧ η ≤ 2 * ε * Real.sqrt e ∧
      0 < T ∧ ContDiff ℝ ∞ v ∧ Function.Periodic v T ∧
      (∀ t, η ≤ v t ∧ v t < 1) ∧
      (∃ t, 0 < t ∧ t < T ∧ v t = η) ∧
      deriv v 0 = 0 ∧ (∀ t, v t ≤ v 0) ∧
      (∀ t, deriv (deriv v) t = v t / 4 - 3 * v t ^ 5 / 4) ∧
      (∀ t, 4 * deriv v t ^ 2 + v t ^ 6 - v t ^ 2 = -(ε ^ 2 * e)) ∧
      (∀ t, |deriv v t| < v t / 2) ∧
      (∀ S, 0 < S → Function.Periodic v S → T ≤ S) := by
  have hq : 0 < ε ^ 2 * e := mul_pos (sq_pos_of_pos hε) he
  obtain ⟨a, ha, hau, henergy, hqa, haq⟩ := exists_squared_neck_of_energy hq hsmall
  let η := Real.sqrt a
  have hη : 0 < η := Real.sqrt_pos.mpr ha
  have hηsq : η ^ 2 = a := Real.sq_sqrt ha.le
  have hηfour : η ^ 4 = a ^ 2 := by rw [show η ^ 4 = (η ^ 2) ^ 2 by ring, hηsq]
  have hηsix : η ^ 6 = a ^ 3 := by rw [show η ^ 6 = (η ^ 2) ^ 3 by ring, hηsq]
  have hsmallη : 3 * η ^ 4 < 1 := by rw [hηfour]; nlinarith
  obtain ⟨v, T, hT, hs, hp, hb, h0, hd0, hmin, hode, hE, hpos, _, hleast⟩ :=
    exists_delaunay_periodic hη hsmallη
  have hsqe := Real.sq_sqrt he.le
  have hsqrte : 0 ≤ Real.sqrt e := Real.sqrt_nonneg e
  refine ⟨η, v, T, hη, ?_, ?_, ?_, hT, hs, hp, ?_, hmin, hd0, ?_, hode, ?_, ?_, hleast⟩
  · rw [hηsq, hηfour]
    nlinarith
  · have hlower : (ε * Real.sqrt e) ^ 2 ≤ η ^ 2 := by
      rw [mul_pow, hsqe, hηsq]
      exact hqa
    exact (sq_le_sq₀ (mul_nonneg hε.le hsqrte) hη.le).mp hlower
  · have hupper : η ^ 2 ≤ (2 * ε * Real.sqrt e) ^ 2 := by
      rw [mul_pow, mul_pow, hsqe, hηsq]
      nlinarith
    exact (sq_le_sq₀ hη.le (by positivity)).mp hupper
  · intro t
    exact ⟨(hb t).1, (hpos t).2.1⟩
  · intro t
    rw [h0]
    exact (hb t).2
  · intro t
    rw [hE, hηsix, hηsq]
    linarith
  · intro t
    exact (hpos t).2.2

#print axioms exists_squared_neck_of_energy
#print axioms exists_delaunay_energy_parameters

end Yamabe3.Analysis.Delaunay
