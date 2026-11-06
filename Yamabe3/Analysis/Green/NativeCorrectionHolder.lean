import Yamabe3.Analysis.Green.LocalH2Holder

/-!
# Pointwise half-Hölder control in the chosen native Green chart

The retained L2 weak inverse supplies its own coordinate H2 regularity in
any specified smooth chart. Native-volume almost-everywhere equality of
its continuous representative is transferred to Lebesgue measure in that
same chart. The resulting Hölder estimate does not change chart or Green
representative and assumes no asymptotic remainder bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set MeasureTheory Metric Filter
open scoped Manifold ContDiff Topology ENNReal

namespace Yamabe3.Analysis.GreenRegularPart

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

/-- The genuine continuous representative of the actual weak inverse is
one-half Hölder near the origin of any specified smooth native chart. In
particular this applies to the very same normalized chart used for Green.
Only the legal native L2 forcing is passed to the H1 inverse. -/
theorem closedL2Solution_holder_half_in_chart
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g)
    (F : Lp ℝ 2 g.volumeMeasure)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target) (he0 : (0 : E) ∈ e.source)
    (U : M → ℝ) (hUc : Continuous U)
    (hUae : U =ᵐ[g.volumeMeasure]
      (toL2 g.leviCivitaData univ (closedConformalLaplacianL2Solution g hY F) : M → ℝ)) :
    ∃ r : ℝ, 0 < r ∧ closedBall (0 : E) r ⊆ e.source ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : E, ‖x‖ < r → ‖U (e x) - U (e 0)‖ ≤ C * ‖x‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds he0)
  let R : ℝ := ε / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hKs : closedBall (0 : E) R ⊆ e.source :=
    (closedBall_subset_ball (by dsimp [R]; linarith : R < ε)).trans hεs
  let w := closedConformalLaplacianL2Solution g hY F
  obtain ⟨W, hW, h0W, hWO, hH2⟩ := exists_coordinate_H2_of_weakForced
    e he hei (isCompact_closedBall (0 : E) R) hKs ball_subset_closedBall isOpen_ball
    (subset_univ _) w (closedLaplacianForcing g F w)
    (closedL2Solution_gradient_forcing g hY F) (mem_ball_self hR)
  have hWK : W ⊆ closedBall (0 : E) R := hWO.trans ball_subset_closedBall
  have hWs : W ⊆ e.source := hWK.trans hKs
  have hUaec := g.ae_comp_on_compact e he hei (isCompact_closedBall (0 : E) R) hKs hUae
  have hUaecW := ae_restrict_of_ae_restrict_of_subset hWK hUaec
  have hUH2 : MemWkp 2 2 (fun y => U (e y)) W :=
    (MemWkp_congr_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2) hW hUaecW).mpr hH2
  have hUcont : ContinuousOn (fun y => U (e y)) W :=
    hUc.comp_continuousOn (e.continuousOn.mono hWs)
  obtain ⟨ρ, hρ, hρW, C, hC, hbound⟩ := exists_holder_half_of_H2 hW hUH2 hUcont h0W
  refine ⟨ρ / 2, half_pos hρ,
    (closedBall_subset_ball (half_lt_self hρ)).trans (hρW.trans hWs), C, hC, ?_⟩
  intro x hx
  have hxρ : x ∈ ball (0 : E) ρ := by
    rw [mem_ball, dist_zero_right]
    linarith
  simpa only [dist_zero_right] using hbound x hxρ 0 (mem_ball_self hρ)

#print axioms closedL2Solution_holder_half_in_chart

end Yamabe3.Analysis.GreenRegularPart
