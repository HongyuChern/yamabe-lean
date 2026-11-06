import Yamabe3.Analysis.Green.NativeNormalDensity
import Yamabe3.Analysis.NativeC2UnitConormal

/-! Normal chart data are produced from the original metric and point.
The coefficient normalization at the origin follows from the true Gauss
identity and continuity, rather than being an extra solver assumption. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter Metric PoincareMT
open scoped Topology Manifold ContDiff Bundle
namespace Yamabe3.Analysis
open EuclideanSphereTrace NormalCoordinates

theorem native_gauss_coefficients_zero (g:RiemannianMetric 3 E)
    (hGauss:∀x v:E,g.inner x x v=inner ℝ x v):
    g.euclideanCoefficients 0=innerSL ℝ:=by
  ext v w
  have hcont:ContinuousAt (fun t:ℝ=>g.euclideanCoefficients (t • v) v w) 0:=by
    have hc:=(g.contDiffAt_euclideanCoefficients (0:E)).continuousAt
    have ht:ContinuousAt (fun t:ℝ=>t • v) 0:=(continuous_id.smul continuous_const).continuousAt
    have ht0:(0:ℝ) • v=(0:E):=zero_smul _ _
    have hct:ContinuousAt (fun t:ℝ=>g.euclideanCoefficients (t • v)) 0:=by
      have hc':ContinuousAt g.euclideanCoefficients ((0:ℝ) • v):=by
        simpa only [zero_smul] using hc
      exact hc'.comp (f:=fun t:ℝ=>t • v) ht
    exact (hct.clm_apply continuousAt_const).clm_apply continuousAt_const
  have he:(fun t:ℝ=>g.euclideanCoefficients (t • v) v w)=ᶠ[𝓝[≠]0](fun _=>inner ℝ v w):=by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h:=hGauss (t • v) w
    change g.euclideanCoefficients (t • v) (t • v) w=inner ℝ (t • v) w at h
    simp only [map_smul,smul_apply,smul_eq_mul,real_inner_smul_left] at h
    exact mul_left_cancel₀ ht h
  have h1:Tendsto (fun t:ℝ=>g.euclideanCoefficients (t • v) v w) (𝓝[≠]0)
      (𝓝 (g.euclideanCoefficients 0 v w)):=by
    simpa only [zero_smul] using hcont.tendsto.mono_left
      (show 𝓝[≠](0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
  have h2:Tendsto (fun t:ℝ=>g.euclideanCoefficients (t • v) v w) (𝓝[≠]0) (𝓝 (inner ℝ v w)):=
    tendsto_const_nhds.congr' he.symm
  change g.euclideanCoefficients 0 v w=inner ℝ v w
  exact tendsto_nhds_unique h1 h2

variable {M:Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

structure NativeLinearChart (g:RiemannianMetric 3 M) (p:M) where
  chart:OpenPartialHomeomorph E M
  radius:ℝ
  metric:RiemannianMetric 3 E
  radius_pos:0<radius
  source:closedBall (0:E) radius⊆chart.source
  center:chart 0=p
  smooth:ContMDiffOn (𝓡 3) (𝓡 3) ∞ chart chart.source
  inverse_smooth:ContMDiffOn (𝓡 3) (𝓡 3) ∞ chart.symm chart.target
  coefficients:∀x∈closedBall (0:E) radius,metric.euclideanCoefficients x=g.pullbackCoefficients chart x
  gauss:∀x v:E,metric.inner x x v=inner ℝ x v
  coefficient_zero:metric.euclideanCoefficients 0=innerSL ℝ
  density_zero:metric.pullbackVolumeDensity id 0=1

theorem exists_native_linear_chart (g:RiemannianMetric 3 M) (p:M):Nonempty (NativeLinearChart g p):=by
  obtain ⟨e,r,gE,_,hr,hs,hp,he,hei,hc,hG,_,_,hρ,_⟩:=exists_native_normalized_density g p
  have hg:∀x v:E,gE.inner x x v=inner ℝ x v:=hG
  exact ⟨⟨e,r,gE,hr,hs,hp,he,hei,hc,hg,native_gauss_coefficients_zero gE hg,hρ⟩⟩

def nativeLinearChart (g:RiemannianMetric 3 M) (p:M):NativeLinearChart g p:=
  Classical.choice (exists_native_linear_chart g p)

#print axioms native_gauss_coefficients_zero
#print axioms exists_native_linear_chart
#print axioms nativeLinearChart
end Yamabe3.Analysis
