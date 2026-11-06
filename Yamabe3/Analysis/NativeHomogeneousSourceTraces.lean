import Yamabe3.Analysis.NativeHomogeneousEntranceTraces
import Yamabe3.Analysis.UniformElliptic.RegularFieldSourceGraphCost
import Yamabe3.Analysis.UniformElliptic.LocalLinearDilation

/-! One homogeneous native field supplies both the original weighted H2
source graph and the actual sphere traces. Its regular field is NOT put
in the decaying H4 correction graph. All costs precede the input field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff Manifold ENNReal RealInnerProductSpace lp
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay PoincareMT.LeviCivitaData.Dirichlet
variable {M : Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def sourceTraceH1Normed (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] sourceTraceH1Normed

theorem exists_nativeHomogeneous_large_entrance_bound
    (g : RiemannianMetric 3 M) (hY : 0<Target.yamabeConstant g) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀ : ℝ} (hR₀ : 0<R₀) (hsource : closedBall (0:E) R₀⊆e.source)
    (hcoeff : ∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hB : gE.euclideanCoefficients 0=innerSL ℝ) (hρ : gE.pullbackVolumeDensity id 0=1) :
    ∃δ : ℝ,0<δ ∧ ∃C : ℝ,0≤C ∧ ∀c a : ℝ,
      Real.log 64≤c → 0<a → a*Real.exp c/2≤R₀ → a*Real.exp c/8<δ →
      ∀(B : M→ℝ) (hBs : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B),
      let Ω := e '' ball (0:E) (a*Real.exp c/2)
      ∀hΩ : IsOpen Ω, (∀x∈Ω,B x=0) →
      let P := nativeHomogeneousChartLinear g B hBs hΩ e a
      (∀W,ContDiffOn ℝ ∞ (P W) (ball (0:E) 5)) ∧
      (∀W,∀x∈ball (0:E) 5,P W x=nativeHomogeneousEnergyRepresentative g B hBs hΩ W (e (a • x))) ∧
      ∀W,∀j≤2,∀x∈closedBall (0:E) 4,
        ‖iteratedFDeriv ℝ j (P W) x‖≤(C*Real.exp (-Real.log a/2))*‖W‖ := by
  obtain ⟨δ,hδ,D,hD,hd⟩ := exists_nativeHomogeneousEnergy_entrance_bound g hY gE e he hei hR₀ hsource hcoeff hB hρ
  refine ⟨δ,hδ,D.toReal,ENNReal.toReal_nonneg,?_⟩
  intro c a hc ha hfit hscale B hBs
  dsimp only
  intro hΩ hzero
  let Ω := e '' ball (0:E) (a*Real.exp c/2)
  let b := 2*a
  let d := c-Real.log 2
  have hb : 0<b := by dsimp only [b];positivity
  have hbd : b*Real.exp d=a*Real.exp c := by
    dsimp only [b,d]
    rw [Real.exp_sub,Real.exp_log (by norm_num:(0:ℝ)<2)]
    ring
  have hd32 : Real.log 32≤d := by
    have hlog : Real.log (64:ℝ)=Real.log 32+Real.log 2 := by
      rw [←Real.log_mul (by norm_num:(32:ℝ)≠0) (by norm_num:(2:ℝ)≠0)]
      norm_num
    dsimp only [d]
    linarith
  have hh := hd d b hd32 hb (by rw [hbd];exact hfit) (by rw [hbd];exact hscale) B hBs
  rw [hbd] at hh
  have hgeom {x:E} (hx : x∈ball (0:E) 3) : b • x∈ball (0:E) (a*Real.exp c/2) := by
    have hn : ‖x‖<3 := by simpa only [mem_ball_zero_iff] using hx
    have hex : 64≤Real.exp c := (Real.exp_log (by norm_num:(0:ℝ)<64)).symm.trans_le (Real.exp_le_exp.mpr hc)
    rw [mem_ball_zero_iff,norm_smul,Real.norm_of_nonneg hb.le]
    dsimp only [b]
    nlinarith [mul_lt_mul_of_pos_left hn ha,mul_le_mul_of_nonneg_left hex ha.le]
  let Pbig := nativeHomogeneousChartLinear g B hBs hΩ e b
  let P := nativeHomogeneousChartLinear g B hBs hΩ e a
  have hPbig : ∀W,ContDiffOn ℝ ∞ (Pbig W) (ball (0:E) 3) :=
    nativeHomogeneousChartLinear_smooth g B hBs hΩ e he b isOpen_ball
      (fun x hx => (ball_subset_closedBall.trans ((closedBall_subset_closedBall hfit).trans hsource)) (hgeom hx))
      (fun x hx => mem_image_of_mem e (hgeom hx))
  have hvalBig W {x:E} (hx:x∈ball (0:E) 3) :
      Pbig W x=nativeHomogeneousEnergyRepresentative g B hBs hΩ W (e (b • x)) :=
    indicator_of_mem (mem_image_of_mem e (hgeom hx)) _
  have hbBig W j (hj:j≤2) x (hx:x∈closedBall (0:E) 2) :
      ‖iteratedFDeriv ℝ j (Pbig W) x‖≤(D.toReal*Real.exp (-Real.log b/2))*‖W‖ := by
    have hx3 : x∈ball (0:E) 3 := closedBall_subset_ball (by norm_num) hx
    have hg : Pbig W =ᶠ[𝓝 x] (fun y => nativeHomogeneousEnergyRepresentative g B hBs hΩ W (e (b • y))) := by
      filter_upwards [isOpen_ball.mem_nhds hx3] with y hy
      exact hvalBig W hy
    have ht := (hh hΩ hzero W).1 j hj x hx
    rw [←(hg.iteratedFDeriv ℝ j).self_of_nhds] at ht
    have htR := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top hD ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top) ht
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _),ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le,mul_assoc] using htR
  have heq : halfDilatedLinear Pbig=P := by
    ext W x
    change nativeHomogeneousEnergyRepresentativeLinear g B hBs hΩ W (e (b • ((1/2:ℝ) • x)))=
      nativeHomogeneousEnergyRepresentativeLinear g B hBs hΩ W (e (a • x))
    rw [smul_smul,show b*(1/2:ℝ)=a by dsimp only [b];ring]
  have hs := halfDilatedLinear_smooth Pbig hPbig
  rw [heq] at hs
  have hj := halfDilatedLinear_two_jet_bound Pbig hPbig (D.toReal*Real.exp (-Real.log b/2))
    (by positivity) hbBig
  rw [heq] at hj
  refine ⟨hs,?_,?_⟩
  · intro W x hx
    change (e '' ball (0:E) (a*Real.exp c/2)).indicator _ (e (a • x))=_
    apply indicator_of_mem
    apply mem_image_of_mem
    have hn : ‖x‖<5 := by simpa only [mem_ball_zero_iff] using hx
    have hex : 64≤Real.exp c := (Real.exp_log (by norm_num:(0:ℝ)<64)).symm.trans_le (Real.exp_le_exp.mpr hc)
    rw [mem_ball_zero_iff,norm_smul,Real.norm_of_nonneg ha.le]
    nlinarith [mul_lt_mul_of_pos_left hn ha,mul_le_mul_of_nonneg_left hex ha.le]
  · intro W j hjj x hx
    apply (hj W j hjj x hx).trans
    have hab : a≤b := by dsimp only [b];linarith
    have he : Real.exp (-Real.log b/2)≤Real.exp (-Real.log a/2) :=
      Real.exp_le_exp.mpr (by linarith [Real.log_le_log ha hab])
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he ENNReal.toReal_nonneg) (norm_nonneg W)

theorem exists_nativeHomogeneous_source_trace_package
    (g : RiemannianMetric 3 M) (hY : 0<Target.yamabeConstant g) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀ : ℝ} (hR₀ : 0<R₀) (hsource : closedBall (0:E) R₀⊆e.source)
    (hcoeff : ∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hB : gE.euclideanCoefficients 0=innerSL ℝ) (hρ : gE.pullbackVolumeDensity id 0=1) :
    ∃δ : ℝ,0<δ ∧ ∃C D : ℝ,0≤C ∧ 0≤D ∧ ∀c a : ℝ,
      Real.log 64≤c → 0<a → a*Real.exp c/2≤R₀ → a*Real.exp c/8<δ →
      ∀(B : M→ℝ) (hBs : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B),
      let Ω := e '' ball (0:E) (a*Real.exp c/2)
      ∀hΩ : IsOpen Ω, (∀x∈Ω,B x=0) →
      let P := nativeHomogeneousChartLinear g B hBs hΩ e a
      ∃hP : ∀W,ContDiffOn ℝ ∞ (P W) (ball (0:E) 3),
      ∃(TS : nativeHomogeneousEnergySpace g B hBs Ω →L[ℝ] HalfEndPhysicalH2SourceGraph)
        (TV TN : nativeHomogeneousEnergySpace g B hBs Ω →L[ℝ] AngularL2),
        ‖TS‖≤D*C*Real.exp (-Real.log a/2) ∧
        (∀W,∀y:HalfEndSourceEntrance,halfEndPhysicalH2SourceGraphValue (TS W) y=
          (radialScale ‖(y:E)‖)⁻¹*nativeHomogeneousEnergyRepresentative g B hBs hΩ W (e (a • (y:E)))) ∧
        (∀W,TV W=nativeSphereL2Inclusion (localLinearSphereValue P hP W)) ∧
        (∀W,TN W=nativeSphereL2Inclusion (localLinearSphereNormal P hP W)) ∧
        ‖TV‖≤‖nativeSphereL2Inclusion‖*(C*Real.exp (-Real.log a/2)) ∧
        ‖TN‖≤‖nativeSphereL2Inclusion‖*(C*Real.exp (-Real.log a/2)) ∧
        ∀W,NativeAngularSpectralRegular (3/2) (TV W) ∧ NativeAngularSpectralRegular (1/2) (TN W) := by
  obtain ⟨δ,hδ,C,hC,hb⟩ := exists_nativeHomogeneous_large_entrance_bound g hY gE e he hei hR₀ hsource hcoeff hB hρ
  refine ⟨δ,hδ,C,regularFieldSourceGraphCost,hC,regularFieldSourceGraphCost_nonneg,?_⟩
  intro c a hc ha hfit hscale B hBs
  dsimp only
  intro hΩ hzero
  obtain ⟨hP5,hval,hjets⟩ := hb c a hc ha hfit hscale B hBs hΩ hzero
  let P := nativeHomogeneousChartLinear g B hBs hΩ e a
  have hP3 : ∀W,ContDiffOn ℝ ∞ (P W) (ball (0:E) 3) :=
    fun W => (hP5 W).mono (ball_subset_ball (by norm_num))
  obtain ⟨TS,hTS,hTSv⟩ := exists_regularField_source_graph_with_cost P hP5
    (C*Real.exp (-Real.log a/2)) (by positivity) hjets
  obtain ⟨TV,TN,hTV,hTN,hTVb,hTNb,htr⟩ := exists_localLinearSphere_trace_maps P hP3
    (C*Real.exp (-Real.log a/2)) (by positivity)
    (fun W j hj x hx => hjets W j hj x (closedBall_subset_closedBall (by norm_num) hx))
  refine ⟨hP3,TS,TV,TN,hTS.trans_eq (by ring),?_,hTV,hTN,hTVb,hTNb,fun W => ⟨(htr W).1,(htr W).2.1⟩⟩
  intro W y
  rw [hTSv]
  change (radialScale ‖(y:E)‖)⁻¹*P W y=_
  rw [hval W y (by rw [mem_ball_zero_iff];linarith [y.2.2])]

#print axioms exists_nativeHomogeneous_large_entrance_bound
#print axioms exists_nativeHomogeneous_source_trace_package
end Yamabe3.Analysis.SpherePolar
