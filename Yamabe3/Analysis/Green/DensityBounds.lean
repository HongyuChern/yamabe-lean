import Yamabe3.Analysis.Green.EuclideanResidual

/-! Bounds needed simultaneously for the residual L² estimate and the
regularized test-integral limit. The constants are obtained from actual
smooth positive functions on compact balls, not supplied as regularity data. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Metric
open scoped ContDiff

namespace Yamabe3.Analysis.GreenParametrix

theorem density_bounds_on_ball {ρ V : E → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x)
    (hzero : fderiv ℝ ρ 0 = 0) (hV : Continuous V)
    {R : ℝ} (hR : 0 < R) :
    ∃ c C B A : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ x ∈ ball (0 : E) R, c ≤ ρ x ∧ ρ x ≤ A ∧
        ‖fderiv ℝ ρ x‖ ≤ C * ‖x‖ ∧ |V x| ≤ B := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ ρ) := hρ.fderiv_right (by simp)
  have hDD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ρ)) := hD.fderiv_right (by simp)
  have hc := isCompact_closedBall (0 : E) R
  have hne : (closedBall (0 : E) R).Nonempty := ⟨0, by simpa using hR.le⟩
  obtain ⟨x0, hx0, hmin⟩ := hc.exists_isMinOn hne hρ.continuous.continuousOn
  obtain ⟨C0, hC0⟩ := hc.exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ ρ)) hDD.continuous.continuousOn
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn hV.continuousOn
  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuousOn hρ.continuous.continuousOn
  refine ⟨ρ x0, max C0 0, B, A, hpos x0, le_max_right _ _, ?_⟩
  intro x hx
  refine ⟨hmin (ball_subset_closedBall hx), (le_abs_self _).trans (hA x (ball_subset_closedBall hx)),
    norm_fderiv_le_mul_norm hR hzero (fun y _ => hD.differentiable (by simp) y)
      (fun y hy => (hC0 y (ball_subset_closedBall hy)).trans (le_max_left _ _)) hx, ?_⟩
  simpa only [Real.norm_eq_abs] using hB x (ball_subset_closedBall hx)

#print axioms density_bounds_on_ball

end Yamabe3.Analysis.GreenParametrix
