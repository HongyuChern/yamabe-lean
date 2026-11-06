import Yamabe3.Analysis.Green.HolderFromH2

/-! # Local half-Hölder control of the actual continuous H2 representative -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set MeasureTheory Metric Filter
open scoped Manifold ContDiff Topology ENNReal

namespace Yamabe3.Analysis.GreenRegularPart

open Poincare.Analysis.Sobolev.Euclidean

private theorem cutoff_two_derivative_bound {η : E → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η) :
    ∃ C : ℝ, ∀ j ≤ 2, ∀ x : E, ‖iteratedFDeriv ℝ j η x‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := (hc.iteratedFDeriv (𝕜 := ℝ) 0).exists_bound_of_continuous
    (hη.continuous_iteratedFDeriv (by exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 0))
  obtain ⟨C₁, hC₁⟩ := (hc.iteratedFDeriv (𝕜 := ℝ) 1).exists_bound_of_continuous
    (hη.continuous_iteratedFDeriv (by exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
  obtain ⟨C₂, hC₂⟩ := (hc.iteratedFDeriv (𝕜 := ℝ) 2).exists_bound_of_continuous
    (hη.continuous_iteratedFDeriv (by exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  refine ⟨max C₀ (max C₁ C₂), fun j hj x => ?_⟩
  interval_cases j
  · exact (hC₀ x).trans (le_max_left _ _)
  · exact (hC₁ x).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hC₂ x).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- In dimension three, the actual continuous representative of a local
W2,2 function obeys a pointwise one-half Hölder estimate near every point.
The exponent comes from W2,2 -> W1,6 and the proved uniform smooth Morrey
bound passed to the actual Sobolev representative. -/
theorem exists_holder_half_of_H2
    {O : Set E} (hO : IsOpen O) {u : E → ℝ}
    (hu : MemWkp 2 2 u O) (huc : ContinuousOn u O) {x : E} (hx : x ∈ O) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ O ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ ball x r, ∀ z ∈ ball x r,
        ‖u y - u z‖ ≤ C * dist y z ^ (1 / 2 : ℝ) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO x hx
  let R : ℝ := ε / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have h2R : 0 < 2 * R := by positivity
  have hballO : ball x (2 * R) ⊆ O :=
    (ball_subset_ball (by dsimp [R]; linarith)).trans hball
  have hinner : closedBall x R ⊆ ball x (2 * R) := closedBall_subset_ball (by linarith)
  obtain ⟨η, hη, hηc, -, hηone, hηsupport, -, -, -⟩ :=
    Poincare.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff_with_fderiv_bound
      (isCompact_closedBall x R) isOpen_ball hinner
  obtain ⟨A, hA⟩ := cutoff_two_derivative_bound hη hηc
  have huBall : MemWkp 2 2 u (ball x (2 * R)) :=
    MemWkp.mono_set (by norm_num : (1 : ℝ≥0∞) ≤ 2) isOpen_ball hballO hu
  have hv : MemWkp 2 2 (fun y => η y * u y) (ball x (2 * R)) :=
    MemWkp.smul_smooth_bounded 2 (by norm_num) isOpen_ball hη
      (fun j hj y _ => hA j hj y) huBall
  have hvc : HasCompactSupport (fun y => η y * u y) := hηc.mul_right
  have hvs : tsupport (fun y => η y * u y) ⊆ ball x (2 * R) :=
    tsupport_mul_subset_left.trans hηsupport
  obtain ⟨h6, -⟩ :=
    Poincare.Analysis.Sobolev.EuclideanEmbedding.TowerStep.MemWkp_succ_subcritical_step
      (d := 3) (k := 1) (p := 2) (by norm_num) (by norm_num) isOpen_ball
      hvc hvs (by simpa using hv)
  have h6' : MemWkp 1 6 (fun y => η y * u y) (ball x (2 * R)) := by
    norm_num at h6 ⊢
    exact h6
  obtain ⟨C, hC, hbound⟩ := holder_half_of_continuous_memW1Six_compact h2R h6'
    (hη.continuous.continuousOn.mul (huc.mono hballO)) hvc hvs
  refine ⟨R, hR, (ball_subset_ball (by linarith)).trans hballO, C, hC, ?_⟩
  intro y hy z hz
  have hy' : y ∈ ball x (2 * R / 2) := by convert hy using 1 <;> ring
  have hz' : z ∈ ball x (2 * R / 2) := by convert hz using 1 <;> ring
  simpa only [hηone y (ball_subset_closedBall hy), hηone z (ball_subset_closedBall hz), one_mul]
    using hbound y hy' z hz'

#print axioms exists_holder_half_of_H2

end Yamabe3.Analysis.GreenRegularPart
