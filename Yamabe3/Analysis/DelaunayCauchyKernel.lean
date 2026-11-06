import Yamabe3.Analysis.DelaunayCauchyPhase
import Yamabe3.Analysis.DelaunayWeightTwoSmallness

/-!
# The actual Cauchy-matched orbit satisfies the common-weight criterion

A single energy threshold and contraction factor work for every original
positive admissible Cauchy orbit. The exact function is identified with its
constructed neck orbit and phase, so the integral bound does not concern a
replacement profile. No phase or minimum-attainment datum is supplied.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

/-- Uniform small true energy controls the same actual orbit's high-mode
potential at decay weight two, without requiring normalized initial data. -/
theorem exists_uniform_small_energy_same_orbit_kernel_bound :
    ∃ (κ q₀ : ℝ), 0 ≤ κ ∧ κ < 1 ∧ 0 < q₀ ∧
      ∀ (v : ℝ → ℝ), ContDiff ℝ ∞ v →
        (∀ t, deriv (deriv v) t = radialForce (v t)) → 0 < v 0 →
        ∀ q : ℝ, 0 < q → q < q₀ →
          q = v 0 ^ 2 - v 0 ^ 6 - 4 * deriv v 0 ^ 2 →
          (∀ t, 0 ≤ v t ∧ v t ≤ 1) ∧
          ∀ t : ℝ, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s *
            ((15 / 4) * v (t - s) ^ 4)) ≤ κ := by
  obtain ⟨κ, hκ0, hκ1, hsmall⟩ := exists_uniform_small_neck_weightTwo_bound
  obtain ⟨r, hr, hrsmall⟩ := Metric.mem_nhdsWithin_iff.mp hsmall
  let q₀ : ℝ := min (3 / 8) (r ^ 2 / 2)
  have hq₀ : 0 < q₀ := lt_min (by norm_num) (div_pos (sq_pos_of_pos hr) (by norm_num))
  refine ⟨κ, q₀, hκ0, hκ1, hq₀, ?_⟩
  intro v hv hode hm q hq hqq hE
  have hqsmall : q < 3 / 8 := hqq.trans_le (min_le_left _ _)
  obtain ⟨η, w, τ, hη, _, _, _, hηq, hw, hw0, hwd0, hwb, hwo, heq, _⟩ :=
    exists_same_cauchy_orbit_neck_phase hv hode hm hq hqsmall hE
  have hηr : η < r := by
    have hqbound : q < r ^ 2 / 2 := hqq.trans_le (min_le_right _ _)
    nlinarith only [hηq, hqbound, hη, hr]
  have hselected := hrsmall (show η ∈ Metric.ball 0 r ∩ Ioi 0 by
    refine ⟨?_, hη⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hη]
    exact hηr)
  have hb (t : ℝ) : 0 ≤ v t ∧ v t ≤ 1 := by
    rw [heq]
    exact ⟨(hη.trans_le (hwb (t + τ)).1).le, (hwb (t + τ)).2.1⟩
  refine ⟨hb, ?_⟩
  intro t
  rw [heq]
  exact hselected.2.2 w hw hw0 hwd0 hwo hwb τ t

end Yamabe3.Analysis.Delaunay
