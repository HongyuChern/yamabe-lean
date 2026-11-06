import Yamabe3.Analysis.NativeHomogeneousReceiverBallH4
import Yamabe3.Analysis.NativeReceiverRepresentativeL2

/-! A uniform genuine native H1-to-interior-H4 receiving estimate.
Constants precede the shrinking source-free ball. The representative
and native completion element are the same at every receiving scale. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Elliptic.InteriorEstimates
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def criticalReceiverH1Normed (g:RiemannianMetric 3 M):
    NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] criticalReceiverH1Normed

theorem exists_nativeCritical_receiver_H4_bound
    (g:RiemannianMetric 3 M) (hY:0<Target.yamabeConstant g) (gE:RiemannianMetric 3 E)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀:ℝ} (hR₀:0<R₀) (hsource:closedBall (0:E) R₀⊆e.source)
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1) :
    ∃δ:ℝ,0<δ ∧ ∃C:ℝ≥0∞,C≠⊤ ∧ ∀R:ℝ,0<R → R≤R₀ →
      ∀(W:H1Zero g.leviCivitaData univ) (Ω:Set M),IsOpen Ω →
      ∀U:M→ℝ,ContMDiffOn (𝓡 3) 𝓘(ℝ,ℝ) ∞ U Ω →
      U=ᵐ[g.volumeMeasure.restrict Ω](toL2 g.leviCivitaData univ W:M→ℝ) →
      (∀x∈ball (0:E) R,e x∈Ω) →
      (∀x∈ball (0:E) R,-8*g.leviCivitaData.laplacian U (e x)+g.leviCivitaData.scalarCurvature (e x)*U (e x)=0) →
      ∀r:ℝ,0<r → r<δ → r*3<R →
      derivativeProfile 2 (ball (0:E) 1) 4 (fun z=>U (e (r • z)))≤
        C*ENNReal.ofReal (Real.exp (-Real.log r/2))*ENNReal.ofReal ‖W‖ := by
  obtain ⟨δ,C,hδ,hC,hb⟩:=exists_nativeHomogeneous_receiver_ball_H4_bound g gE e he hei hB hρ
  obtain ⟨D,hD,hd⟩:=exists_nativeRepresentative_rescaled_receiver_L2_bound g hY e he hei
    (isCompact_closedBall (0:E) R₀) hsource (ball (0:E) 2) measurableSet_ball measure_ball_lt_top
  refine ⟨δ,hδ,ENNReal.ofReal C*D,by finiteness,fun R hR hRR W Ω hΩ U hU hAE hΩR hP r hr hrδ hrR=>?_⟩
  have hsourceR:closedBall (0:E) R⊆e.source:=(closedBall_subset_closedBall hRR).trans hsource
  have hcoeffR:∀x∈closedBall (0:E) R,gE.euclideanCoefficients x=g.pullbackCoefficients e x:=
    fun x hx=>hcoeff x (closedBall_subset_closedBall hRR hx)
  have hmapR:MapsTo (fun z:E=>r • z) (ball (0:E) 2) (ball (0:E) R):=by
    intro z hz
    have hz2:‖z‖<2:=by simpa using hz
    rw [mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg hr.le]
    exact (mul_lt_mul_of_pos_left hz2 hr).trans (by linarith only [hr,hrR])
  have hmap:MapsTo (fun z:E=>Real.exp (Real.log r) • z) (ball (0:E) 2) (closedBall (0:E) R₀):=by
    rw [Real.exp_log hr]
    exact hmapR.mono_right (ball_subset_closedBall.trans (closedBall_subset_closedBall hRR))
  have hmapΩ:∀x∈ball (0:E) 2,e (Real.exp (Real.log r) • x)∈Ω:=by
    rw [Real.exp_log hr]
    exact fun x hx=>hΩR _ (hmapR hx)
  have hl:=hd W (Real.log r) hmap Ω hΩ.measurableSet U hAE hmapΩ
  rw [Real.exp_log hr] at hl
  have hs:∀x∈ball (0:E) R,ContMDiffAt (𝓡 3) 𝓘(ℝ,ℝ) ∞ U (e x):=
    fun x hx=>hU.contMDiffAt (hΩ.mem_nhds (hΩR x hx))
  exact (hb R hR hsourceR hcoeffR r hr hrδ hrR U hs hP).trans
    ((mul_le_mul le_rfl hl.2 zero_le zero_le).trans_eq (by ring))

#print axioms exists_nativeCritical_receiver_H4_bound
end Yamabe3.Analysis.SpherePolar
