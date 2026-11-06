import Yamabe3.Analysis.NativeHomogeneousSourceTraces
import Yamabe3.Analysis.QuarterDilationBallProfile

/-! The same native homogeneous field has an ACTUAL H4 profile on the
whole radius-four entrance ball. The larger receiving scale is paid
before the input field and before the small physical scale. -/
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
private def largeH4H1Normed (g:RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] largeH4H1Normed

theorem exists_nativeHomogeneous_large_H4_profile
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
      ∀hΩ:IsOpen Ω, (∀x∈Ω,B x=0) → ∀W:nativeHomogeneousEnergySpace g B hBs Ω,
        derivativeProfile 2 (ball (0:E) 4) 4 (nativeHomogeneousChartLinear g B hBs hΩ e a W)≤
          ENNReal.ofReal (C*Real.exp (-Real.log a/2)*‖W‖) := by
  obtain ⟨δ,hδ,D,hD,hd⟩:=exists_nativeHomogeneousEnergy_entrance_bound g hY gE e he hei hR₀ hsource hcoeff hB hρ
  refine ⟨δ,64*D.toReal,hδ,by positivity,?_⟩
  intro c a hc ha hfit hscale B hBs
  dsimp only
  intro hΩ hzero W
  let b:=4*a
  let d:=c-Real.log 4
  have hb:0<b := by dsimp only [b];positivity
  have hbd:b*Real.exp d=a*Real.exp c := by
    dsimp only [b,d]
    rw [Real.exp_sub,Real.exp_log (by norm_num:(0:ℝ)<4)]
    ring
  have hd32:Real.log 32≤d := by
    have hlog:Real.log (128:ℝ)=Real.log 32+Real.log 4 := by
      rw [←Real.log_mul (by norm_num:(32:ℝ)≠0) (by norm_num:(4:ℝ)≠0)]
      norm_num
    dsimp only [d]
    linarith
  have hh:=hd d b hd32 hb (by rw [hbd];exact hfit) (by rw [hbd];exact hscale) B hBs
  rw [hbd] at hh
  have hest:derivativeProfile 2 (ball (0:E) 1) 4
      (fun x=>nativeHomogeneousEnergyRepresentative g B hBs hΩ W (e (b • x)))≤
      D*ENNReal.ofReal (Real.exp (-Real.log b/2))*ENNReal.ofReal ‖W‖ := (hh hΩ hzero W).2
  have hgeom {x:E} (hx:x∈ball (0:E) 3):b • x∈ball (0:E) (a*Real.exp c/2) := by
    have hn:‖x‖<3 := by simpa only [mem_ball_zero_iff] using hx
    have hex:128≤Real.exp c := (Real.exp_log (by norm_num:(0:ℝ)<128)).symm.trans_le (Real.exp_le_exp.mpr hc)
    rw [mem_ball_zero_iff,norm_smul,Real.norm_of_nonneg hb.le]
    dsimp only [b]
    nlinarith [mul_lt_mul_of_pos_left hn ha,mul_le_mul_of_nonneg_left hex ha.le]
  let P:=nativeHomogeneousChartLinear g B hBs hΩ e b
  have hP:ContDiffOn ℝ ∞ (P W) (ball (0:E) 3) :=
    nativeHomogeneousChartLinear_smooth g B hBs hΩ e he b isOpen_ball
      (fun x hx => (ball_subset_closedBall.trans ((closedBall_subset_closedBall hfit).trans hsource)) (hgeom hx))
      (fun x hx => mem_image_of_mem e (hgeom hx)) W
  have hval {x:E} (hx:x∈ball (0:E) 3):P W x=
      nativeHomogeneousEnergyRepresentative g B hBs hΩ W (e (b • x)) :=
    indicator_of_mem (mem_image_of_mem e (hgeom hx)) _
  have hprofile:derivativeProfile 2 (ball (0:E) 1) 4 (P W)≤
      D*ENNReal.ofReal (Real.exp (-Real.log b/2))*ENNReal.ofReal ‖W‖ := by
    rw [derivativeProfile_eq_of_local_germs measurableSet_ball
      (fun x hx => by
        filter_upwards [isOpen_ball.mem_nhds ((ball_subset_ball (by norm_num:(1:ℝ)≤3)) hx)] with y hy
        exact hval hy) 2 4]
    exact hest
  have hquarter:=derivativeProfile_quarter_dilation_ball_le hP 4
  have heq:(fun x:E=>P W ((1/4:ℝ) • x))=nativeHomogeneousChartLinear g B hBs hΩ e a W := by
    funext x
    change nativeHomogeneousEnergyRepresentativeLinear g B hBs hΩ W (e (b • ((1/4:ℝ) • x)))=_
    rw [smul_smul,show b*(1/4:ℝ)=a by dsimp only [b];ring]
    rfl
  rw [heq] at hquarter
  have he:Real.exp (-Real.log b/2)≤Real.exp (-Real.log a/2) :=
    Real.exp_le_exp.mpr (by linarith [Real.log_le_log ha (show a≤b by dsimp only [b];linarith)])
  have hD':D=ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hD).symm
  apply (hquarter.trans (mul_le_mul_of_nonneg_left hprofile zero_le)).trans
  rw [hD']
  simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  rw [ENNReal.ofReal_mul (by positivity:0≤64*D.toReal*Real.exp (-Real.log a/2)),
    ENNReal.ofReal_mul (by positivity:0≤64*D.toReal),ENNReal.ofReal_mul (by norm_num:(0:ℝ)≤64)]
  norm_num only [ENNReal.ofReal_ofNat]
  calc
    _ ≤ 64*(ENNReal.ofReal D.toReal*ENNReal.ofReal (Real.exp (-Real.log a/2))*ENNReal.ofReal ‖W‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal he) zero_le) zero_le) zero_le
    _ = _ := by ring

#print axioms exists_nativeHomogeneous_large_H4_profile
end Yamabe3.Analysis.SpherePolar
