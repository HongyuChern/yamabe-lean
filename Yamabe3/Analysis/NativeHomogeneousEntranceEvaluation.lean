import Yamabe3.Analysis.NativeHomogeneousEnergyEntrance

/-! Genuine bounded linear evaluations of the same regular energy
representative, with the a^(-1/2) entrance cost derived upstream.
These are interior values, not evaluations of arbitrary L2 classes. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff Manifold ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {M : Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def homogeneousEvaluationH1Normed (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] homogeneousEvaluationH1Normed

theorem exists_nativeHomogeneous_entrance_evaluation
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hsource : closedBall (0 : E) R₀ ⊆ e.source)
    (hcoeff : ∀x∈closedBall (0 : E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hB : gE.euclideanCoefficients 0=innerSL ℝ) (hρ : gE.pullbackVolumeDensity id 0=1) :
    ∃δ : ℝ, 0 < δ ∧ ∃C : ℝ, 0 ≤ C ∧ ∀(c a : ℝ),
      Real.log 32 ≤ c → 0 < a → a*Real.exp c/2 ≤ R₀ → a*Real.exp c/8 < δ →
      ∀(B : M → ℝ) (hBs : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B),
      let Ω := e '' ball (0 : E) (a*Real.exp c/2)
      ∀hΩ : IsOpen Ω, (∀y∈Ω,B y=0) → ∀x∈closedBall (0 : E) 2,
      ∃L : nativeHomogeneousEnergySpace g B hBs Ω →L[ℝ] ℝ,
        (∀W,L W=nativeHomogeneousEnergyRepresentative g B hBs hΩ W (e (a • x))) ∧
          ‖L‖ ≤ C*Real.exp (-Real.log a/2) := by
  obtain ⟨δ,hδ,C,hC,h⟩ := exists_nativeHomogeneousEnergy_entrance_bound g hY gE e he hei hR₀ hsource hcoeff hB hρ
  refine ⟨δ,hδ,C.toReal,ENNReal.toReal_nonneg,fun c a hc ha hfit hscale B hBs => ?_⟩
  dsimp only
  intro hΩ hzero x hx
  let Ω := e '' ball (0 : E) (a*Real.exp c/2)
  let P := nativeHomogeneousEnergyRepresentativeLinear g B hBs hΩ
  let Q : nativeHomogeneousEnergySpace g B hBs Ω →ₗ[ℝ] ℝ :=
    { toFun := fun W => P W (e (a • x))
      map_add' := fun W Z => by rw [map_add];rfl
      map_smul' := fun d W => by rw [map_smul];rfl }
  have hec : 32 ≤ Real.exp c :=
    (Real.exp_log (by norm_num : (0 : ℝ) < 32)).symm.trans_le (Real.exp_le_exp.mpr hc)
  have hy : e (a • x)∈Ω := by
    apply mem_image_of_mem
    rw [mem_ball_zero_iff,norm_smul,Real.norm_of_nonneg ha.le]
    have hxn : ‖x‖ ≤ 2 := by simpa only [mem_closedBall,dist_zero_right] using hx
    exact (mul_le_mul_of_nonneg_left hxn ha.le).trans_lt (by have hp := mul_le_mul_of_nonneg_left hec ha.le; nlinarith only [hp,ha])
  have hval (W : nativeHomogeneousEnergySpace g B hBs Ω) : Q W=
      nativeHomogeneousEnergyRepresentative g B hBs hΩ W (e (a • x)) := by
    exact indicator_of_mem hy _
  have hb (W : nativeHomogeneousEnergySpace g B hBs Ω) :
      ‖Q W‖ ≤ (C.toReal*Real.exp (-Real.log a/2))*‖W‖ := by
    have hh := (h c a hc ha hfit hscale B hBs hΩ hzero W).1 0 (by norm_num) x hx
    simp only [norm_iteratedFDeriv_zero] at hh
    rw [← hval W] at hh
    have ht := ENNReal.toReal_mono (by finiteness) hh
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (norm_nonneg _),
      ENNReal.toReal_ofReal (Real.exp_pos _).le] using ht
  let L := Q.mkContinuous (C.toReal*Real.exp (-Real.log a/2)) hb
  refine ⟨L,hval,?_⟩
  exact LinearMap.mkContinuous_norm_le _ (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le) hb

#print axioms exists_nativeHomogeneous_entrance_evaluation
end Yamabe3.Analysis.SpherePolar
