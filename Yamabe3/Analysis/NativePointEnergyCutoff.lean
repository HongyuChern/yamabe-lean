import Yamabe3.Analysis.NativeCompletedChartScaling
import Mathlib.Analysis.SpecificLimits.Normed

/-! Actual native smooth point cutoffs in real dimension3. A fixed
Euclidean bump is genuinely dilated and chart-transported. Its energy
norm is bounded by C sqrt(a), with one fixed chart cost. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open Set Filter MeasureTheory Metric PoincareMT UniformSpace
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
local notation "D" => nativeWeakEuclideanD
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

def nativePointBumpTest (β:ContDiffBump (0:E)) : EnergyTest D (closedBall (0:E) β.rOut) :=
  ⟨β,β.contDiff.contMDiff,β.hasCompactSupport,by rw [β.tsupport_eq]⟩

def nativeChartPointCutoffTest
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (β:ContDiffBump (0:E)) {a:ℝ} (ha:0<a)
    (hfit:euclideanDilatedDomain a (closedBall (0:E) β.rOut)⊆e.source) :
    EnergyTest g.leviCivitaData univ :=
  testInclusion (subset_univ (e '' euclideanDilatedDomain a (closedBall (0:E) β.rOut)))
    (nativeWeakChartTest g e hei hfit (euclideanDilatedTest ha _ (nativePointBumpTest β)))

theorem nativeChartPointCutoffTest_germ
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (β:ContDiffBump (0:E)) {a:ℝ} (ha:0<a)
    (hfit:euclideanDilatedDomain a (closedBall (0:E) β.rOut)⊆e.source) :
    (nativeChartPointCutoffTest g e hei β ha hfit:M→ℝ)=ᶠ[𝓝 (e 0)](fun _=>1) := by
  have h0s:(0:E)∈e.source:=hfit (by
    change a⁻¹ • (0:E)∈closedBall (0:E) β.rOut
    simpa only [smul_zero,mem_closedBall,dist_self] using β.rOut_pos.le)
  have h0t:=e.map_source h0s
  have hz:a⁻¹ • e.symm (e 0)=(0:E):=by rw [e.left_inv h0s,smul_zero]
  have hβ1:(β:E→ℝ)=ᶠ[𝓝 (0:E)](fun _=>1):=by
    filter_upwards [isOpen_ball.mem_nhds (show (0:E)∈ball (0:E) β.rIn by simpa using β.rIn_pos)] with x hx
    exact β.one_of_mem_closedBall (ball_subset_closedBall hx)
  have ht:Tendsto (fun y:M=>a⁻¹ • e.symm y) (𝓝 (e 0)) (𝓝 (0:E)):=by
    have hh:=((e.symm.continuousOn.continuousAt (e.open_target.mem_nhds h0t)).const_smul a⁻¹).tendsto
    change Tendsto (fun y:M=>a⁻¹ • e.symm y) (𝓝 (e 0)) (𝓝 (a⁻¹ • e.symm (e 0))) at hh
    simpa only [hz] using hh
  have hcomp:=ht.eventually hβ1
  have heq:=coordinateExtension_eventuallyEq e (fun x:E=>β (a⁻¹ • x)) h0t
  filter_upwards [heq,hcomp] with y hy hb
  change coordinateExtension e (fun x:E=>β (a⁻¹ • x)) y=1
  exact hy.trans hb

theorem nativeChartPointCutoffTest_norm
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (β:ContDiffBump (0:E)) {a:ℝ} (ha:0<a) (ha1:a≤1)
    (hfit:euclideanDilatedDomain a (closedBall (0:E) β.rOut)⊆K) :
    ‖nativeChartPointCutoffTest g e hei β ha (hfit.trans hKs)‖≤
      (nativeWeakChartBound g e he hei hK hKs*‖nativePointBumpTest β‖)*Real.sqrt a := by
  change ‖testInclusion _ (nativeWeakChartTest g e hei _ (euclideanDilatedTest ha _ (nativePointBumpTest β)))‖≤_
  rw [LinearIsometry.norm_map]
  exact ((nativeWeakChartTest_norm_le g e he hei hK hKs hfit _).trans
    (mul_le_mul_of_nonneg_left (euclideanDilatedTest_norm_le ha ha1 _ (nativePointBumpTest β))
      (nativeWeakChartBound_pos g e he hei hK hKs).le)).trans_eq (by ring)

#print axioms nativeChartPointCutoffTest_germ
#print axioms nativeChartPointCutoffTest_norm
end Yamabe3.Analysis.SpherePolar
