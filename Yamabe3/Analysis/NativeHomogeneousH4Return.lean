import Yamabe3.Analysis.NativeHomogeneousLargeH4Profile
import Yamabe3.Analysis.LocalTaylorH4Return

/-! The SAME native homogeneous energy field returns boundedly to its
actual four low jets and weighted H4 remainder. The a^(-1/2) cost is
explicit, uniform before the input field; no realization is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff Manifold ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Poincare.Analysis.Elliptic.InteriorEstimates PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def homogeneousH4ReturnH1Normed (g:RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] homogeneousH4ReturnH1Normed

private theorem return_cost_mul (C B r:ℝ) (hr:0≤r) :
    localTaylorH4ReturnCost (C*r) (B*r)=localTaylorH4ReturnCost C B*r := by
  unfold localTaylorH4ReturnCost zeroFirstJetH4GraphCost firstTaylorRemainderProfileCost
  rw [max_mul_of_nonneg _ _ hr,max_mul_of_nonneg _ _ hr]
  congr 1
  congr 1 <;> ring

theorem exists_nativeHomogeneous_H4_return
    (g:RiemannianMetric 3 M) (hY:0<Target.yamabeConstant g) (gE:RiemannianMetric 3 E)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀:ℝ} (hR₀:0<R₀) (hsource:closedBall (0:E) R₀⊆e.source)
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1) :
    ∃δ C:ℝ,0<δ ∧ 0≤C ∧ ∀c a:ℝ,
      Real.log 128≤c → 0<a → a*Real.exp c/2≤R₀ → a*Real.exp c/8<δ →
      ∀(B:M→ℝ) (hBs:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B),
      let Ω:=e '' ball (0:E) (a*Real.exp c/2)
      ∀hΩ:IsOpen Ω, (∀x∈Ω,B x=0) →
      ∃T:nativeHomogeneousEnergySpace g B hBs Ω →L[ℝ] RegularLowH4Space,
        ‖T‖≤C*Real.exp (-Real.log a/2) ∧
        ∀W,EqOn (regularLowH4Field (T W))
          (fun x:E=>nativeHomogeneousEnergyRepresentative g B hBs hΩ W (e (a • x)))
          (closedBall (0:E) 4) := by
  obtain ⟨δ₁,hδ₁,D,hD,hd⟩:=exists_nativeHomogeneous_large_entrance_bound g hY gE e he hei hR₀ hsource hcoeff hB hρ
  obtain ⟨δ₂,J,hδ₂,hJ,hj⟩:=exists_nativeHomogeneous_large_H4_profile g hY gE e he hei hR₀ hsource hcoeff hB hρ
  refine ⟨min δ₁ δ₂,localTaylorH4ReturnCost D J,lt_min hδ₁ hδ₂,localTaylorH4ReturnCost_nonneg hD,?_⟩
  intro c a hc ha hfit hscale B hBs
  dsimp only
  intro hΩ hzero
  have hc64:Real.log 64≤c := (Real.log_le_log (by norm_num:(0:ℝ)<64) (by norm_num:(64:ℝ)≤128)).trans hc
  obtain ⟨hP,hval,hjets⟩:=hd c a hc64 ha hfit (hscale.trans_le (min_le_left _ _)) B hBs hΩ hzero
  have hp:=hj c a hc ha hfit (hscale.trans_le (min_le_right _ _)) B hBs hΩ hzero
  obtain ⟨T,hT,_,hTv⟩:=exists_localTaylorH4Return
    (nativeHomogeneousChartLinear g B hBs hΩ e a) hP
    (D*Real.exp (-Real.log a/2)) (J*Real.exp (-Real.log a/2)) (by positivity) (by positivity)
    hjets hp
  rw [return_cost_mul D J _ (Real.exp_pos _).le] at hT
  refine ⟨T,hT,fun W x hx => (hTv W hx).trans ?_⟩
  exact hval W x ((closedBall_subset_ball (by norm_num:(4:ℝ)<5)) hx)

#print axioms exists_nativeHomogeneous_H4_return
end Yamabe3.Analysis.SpherePolar
