import Yamabe3.Analysis.NativeHomogeneousEntranceGraph
import Yamabe3.Analysis.UniformElliptic.LocalLinearSphereTraces

/-! Bounded value and normal traces of the same actual homogeneous
native field, with quantitative three-halves/half spectral budgets.
These are literal smooth interior sphere traces, not restrictions of L2
representatives or a claim of original-metric conormal cancellation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff Manifold ENNReal BigOperators RealInnerProductSpace lp
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay Poincare.Geometry.Riemannian.SpaceForm
open PoincareMT.LeviCivitaData.Dirichlet
variable {M : Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def entranceTraceH1Normed (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] entranceTraceH1Normed

def nativeHomogeneousChartLinear (g : RiemannianMetric 3 M) (B : M→ℝ)
    (hBs : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B) {Ω : Set M} (hΩ : IsOpen Ω)
    (e : OpenPartialHomeomorph E M) (a : ℝ) :
    nativeHomogeneousEnergySpace g B hBs Ω →ₗ[ℝ] (E→ℝ) where
  toFun W x := nativeHomogeneousEnergyRepresentativeLinear g B hBs hΩ W (e (a • x))
  map_add' W Z := by funext x;rw [map_add];rfl
  map_smul' c W := by funext x;rw [map_smul];rfl

theorem nativeHomogeneousChartLinear_smooth
    (g : RiemannianMetric 3 M) (B : M→ℝ)
    (hBs : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B) {Ω : Set M} (hΩ : IsOpen Ω)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source) (a : ℝ)
    {O : Set E} (hO : IsOpen O)
    (hsource : ∀x∈O,a • x∈e.source) (hmap : ∀x∈O,e (a • x)∈Ω)
    (W : nativeHomogeneousEnergySpace g B hBs Ω) :
    ContDiffOn ℝ ∞ (nativeHomogeneousChartLinear g B hBs hΩ e a W) O := by
  let U := nativeHomogeneousEnergyRepresentative g B hBs hΩ W
  have hU := nativeHomogeneousEnergyRepresentative_spec g B hBs hΩ W
  have hreg : ContDiffOn ℝ ∞ (fun x => U (e (a • x))) O := by
    intro x hx
    have heAt := he.contMDiffAt (e.open_source.mem_nhds (hsource x hx))
    have huAt := hU.1.contMDiffAt (hΩ.mem_nhds (hmap x hx))
    exact ((contMDiffAt_iff_contDiffAt.mp (huAt.comp _ heAt)).comp x
      (contDiff_id.const_smul a).contDiffAt).contDiffWithinAt
  apply hreg.congr
  intro x hx
  exact indicator_of_mem (hmap x hx) _

theorem exists_nativeHomogeneous_entrance_trace_maps
    (g : RiemannianMetric 3 M) (hY : 0<Target.yamabeConstant g) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀ : ℝ} (hR₀ : 0<R₀) (hsource : closedBall (0:E) R₀⊆e.source)
    (hcoeff : ∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hB : gE.euclideanCoefficients 0=innerSL ℝ) (hρ : gE.pullbackVolumeDensity id 0=1) :
    ∃δ : ℝ,0<δ ∧ ∃C : ℝ,0≤C ∧ ∀c a : ℝ,
      Real.log 32≤c → 0<a → a*Real.exp c/2≤R₀ → a*Real.exp c/8<δ →
      ∀(B : M→ℝ) (hBs : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B),
      let Ω := e '' ball (0:E) (a*Real.exp c/2)
      ∀hΩ : IsOpen Ω, (∀x∈Ω,B x=0) →
      let P := nativeHomogeneousChartLinear g B hBs hΩ e a
      (∀W,∀x∈ball (0:E) 3,P W x=nativeHomogeneousEnergyRepresentative g B hBs hΩ W (e (a • x))) ∧
      ∃hP : ∀W,ContDiffOn ℝ ∞ (P W) (ball (0:E) 3),
      ∃(T N : nativeHomogeneousEnergySpace g B hBs Ω →L[ℝ] AngularL2),
        (∀W,T W=nativeSphereL2Inclusion (localLinearSphereValue P hP W)) ∧
        (∀W,N W=nativeSphereL2Inclusion (localLinearSphereNormal P hP W)) ∧
        ‖T‖≤‖nativeSphereL2Inclusion‖*(C*Real.exp (-Real.log a/2)) ∧
        ‖N‖≤‖nativeSphereL2Inclusion‖*(C*Real.exp (-Real.log a/2)) ∧
        ∀W,NativeAngularSpectralRegular (3/2) (T W) ∧ NativeAngularSpectralRegular (1/2) (N W) ∧
          (∑'i,nativeAngularWeightedSquare (3/2) (T W) i)≤
            74*((roundSphereMetric 2).volumeMeasure univ).toReal*((C*Real.exp (-Real.log a/2))*‖W‖)^2 ∧
          (∑'i,nativeAngularWeightedSquare (1/2) (N W) i)≤
            5*((roundSphereMetric 2).volumeMeasure univ).toReal*((C*Real.exp (-Real.log a/2))*‖W‖)^2 := by
  obtain ⟨δ,hδ,D,hD,hd⟩ := exists_nativeHomogeneousEnergy_entrance_bound g hY gE e he hei hR₀ hsource hcoeff hB hρ
  refine ⟨δ,hδ,D.toReal,ENNReal.toReal_nonneg,?_⟩
  intro c a hc ha hfit hscale B hBs
  dsimp only
  intro hΩ hzero
  let Ω := e '' ball (0:E) (a*Real.exp c/2)
  let P := nativeHomogeneousChartLinear g B hBs hΩ e a
  have hax {x : E} (hx : x∈ball (0:E) 3) : a • x∈ball (0:E) (a*Real.exp c/2) := by
    rw [mem_ball_zero_iff,norm_smul,Real.norm_of_nonneg ha.le]
    have hn : ‖x‖<3 := by simpa only [mem_ball_zero_iff] using hx
    have hec : 32≤Real.exp c := (Real.exp_log (by norm_num:(0:ℝ)<32)).symm.trans_le (Real.exp_le_exp.mpr hc)
    nlinarith [mul_lt_mul_of_pos_left hn ha,mul_le_mul_of_nonneg_left hec ha.le]
  have hy {x : E} (hx : x∈ball (0:E) 3) : e (a • x)∈Ω := mem_image_of_mem e (hax hx)
  have hval (W : nativeHomogeneousEnergySpace g B hBs Ω) {x : E} (hx : x∈ball (0:E) 3) :
      P W x=nativeHomogeneousEnergyRepresentative g B hBs hΩ W (e (a • x)) :=
    indicator_of_mem (hy hx) _
  have hP : ∀W,ContDiffOn ℝ ∞ (P W) (ball (0:E) 3) :=
    nativeHomogeneousChartLinear_smooth g B hBs hΩ e he a isOpen_ball
      (fun x hx => (ball_subset_closedBall.trans ((closedBall_subset_closedBall hfit).trans hsource)) (hax hx))
      (fun x hx => hy hx)
  have hb (W : nativeHomogeneousEnergySpace g B hBs Ω) (j : ℕ) (hj : j≤2)
      (x : E) (hx : x∈closedBall (0:E) 2) :
      ‖iteratedFDeriv ℝ j (P W) x‖≤(D.toReal*Real.exp (-Real.log a/2))*‖W‖ := by
    have hx3 : x∈ball (0:E) 3 := closedBall_subset_ball (by norm_num) hx
    have hge : P W =ᶠ[𝓝 x] (fun y => nativeHomogeneousEnergyRepresentative g B hBs hΩ W (e (a • y))) :=
      by
        filter_upwards [isOpen_ball.mem_nhds hx3] with y hy
        exact hval W hy
    have hh := (hd c a hc ha hfit hscale B hBs hΩ hzero W).1 j hj x hx
    rw [←(hge.iteratedFDeriv ℝ j).self_of_nhds] at hh
    have ht := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top hD ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top) hh
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _),ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le,mul_assoc] using ht
  exact ⟨fun W x hx => hval W hx,hP,exists_localLinearSphere_trace_maps P hP
    (D.toReal*Real.exp (-Real.log a/2)) (by positivity) hb⟩

#print axioms nativeHomogeneousChartLinear
#print axioms nativeHomogeneousChartLinear_smooth
#print axioms exists_nativeHomogeneous_entrance_trace_maps
end Yamabe3.Analysis.SpherePolar
