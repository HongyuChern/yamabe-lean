import Yamabe3.Analysis.NativeHomogeneousH4Return

/-! The actual H4 return cost cancels the physical sqrt(a) source/energy
scale. Every output represents the SAME input native field on the whole
receiving core, retaining its genuine low jets and H4 remainder. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff Manifold ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def returnCompositionH1Normed (g:RiemannianMetric 3 M):NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] returnCompositionH1Normed

theorem exp_negative_half_log_mul_sqrt {a:ℝ} (ha:0 < a) :
    Real.exp (-Real.log a/2)*Real.sqrt a=1 := by
  rw [neg_div,Real.exp_neg,Real.exp_half,Real.exp_log ha,inv_mul_cancel₀ (Real.sqrt_pos.mpr ha).ne']

theorem exists_nativeHomogeneous_small_H4_composition
    (g:RiemannianMetric 3 M) (hY:0 < Target.yamabeConstant g) (gE:RiemannianMetric 3 E)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀:ℝ} (hR₀:0 < R₀) (hsource:closedBall (0:E) R₀⊆e.source)
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1) :
    ∃δ C:ℝ,0 < δ ∧ 0 ≤ C ∧ ∀c a:ℝ,
      Real.log 128 ≤ c → 0 < a → a*Real.exp c/2 ≤ R₀ → a*Real.exp c/8 < δ →
      ∀(B:M→ℝ) (hBs:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B),
      let Ω:=e '' ball (0:E) (a*Real.exp c/2)
      ∀hΩ:IsOpen Ω,(∀x∈Ω,B x=0) →
      ∀(X:Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
        (R:X →L[ℝ] nativeHomogeneousEnergySpace g B hBs Ω)
        (A ε:ℝ),0 ≤ A → 0 ≤ ε → ‖R‖ ≤ A*Real.sqrt a*ε →
      ∃T:X →L[ℝ] RegularLowH4Space,‖T‖ ≤ C*A*ε ∧
        ∀x:X,EqOn (regularLowH4Field (T x))
          (fun y:E=>nativeHomogeneousEnergyRepresentative g B hBs hΩ (R x) (e (a • y)))
          (closedBall (0:E) 4) := by
  obtain ⟨δ,C,hδ,hC,hret⟩:=exists_nativeHomogeneous_H4_return g hY gE e he hei hR₀ hsource hcoeff hB hρ
  refine ⟨δ,C,hδ,hC,?_⟩
  intro c a hc ha hfit hscale B hBs
  dsimp only
  intro hΩ hzero X _ _ R A ε hA hε hR
  obtain ⟨J,hJ,hJv⟩:=hret c a hc ha hfit hscale B hBs hΩ hzero
  let T:=J.comp R
  have hbound:‖T‖ ≤ C*A*ε := by
    apply (ContinuousLinearMap.opNorm_comp_le J R).trans
    apply (mul_le_mul hJ hR (norm_nonneg R) (mul_nonneg hC (Real.exp_pos _).le)).trans_eq
    calc
      _ = (C*A*ε)*(Real.exp (-Real.log a/2)*Real.sqrt a) := by ring
      _ = _ := by rw [exp_negative_half_log_mul_sqrt ha,mul_one]
  exact ⟨T,hbound,fun x=>hJv (R x)⟩

#print axioms exp_negative_half_log_mul_sqrt
#print axioms exists_nativeHomogeneous_small_H4_composition
end Yamabe3.Analysis.SpherePolar
