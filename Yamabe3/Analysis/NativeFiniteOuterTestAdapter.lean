import Yamabe3.Analysis.NativeFiniteOuterOpenAnnulus
import Yamabe3.Analysis.NativeH2ChartWeakEquation

/-! Every native compact test inside the actual finite exterior annulus
has a genuine smooth Euclidean exterior test with the SAME values on
the chart. Its support avoids zero and vanishes off the chart. No test
adaptation is left as an extra main-theorem assumption. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Manifold Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic ChartOperatorTransfer NativeChartSphereMetric
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

 theorem exists_nativeFiniteOuter_smooth_test_adapter
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (R₀:ℝ) (hKs:closedBall (0:E) R₀⊆e.source)
    {a:ℝ} (ha:0<a) (N:ℕ) (hfit:a*Real.exp ((N:ℝ)/2+1)≤R₀)
    (η:EnergyTest g.leviCivitaData univ)
    (hη:tsupport (η:M→ℝ)⊆e '' nativeFiniteOuterOpenAnnulus a N):
    ∃φ:E→ℝ,∃hφ:ContDiff ℝ ∞ φ,∃hc:HasCompactSupport φ,∃h0:(0:E)∉tsupport φ,
      tsupport φ⊆{x:E|1<‖x‖} ∧
      (∀y∈closedBall (0:E) R₀,φ (a⁻¹ • y)=η (e y)) ∧
      (∀y:E,y∉closedBall (0:E) R₀→φ (a⁻¹ • y)=0):=by
  have hAK:=nativeFiniteOuterOpenAnnulus_chart_fit ha N hfit
  have hAs:(nativeFiniteOuterOpenAnnulus a N)⊆e.source:=hAK.trans hKs
  have hηtarget:tsupport (η:M→ℝ)⊆e.target:=by
    intro y hy
    obtain ⟨x,hx,rfl⟩:=hη hy
    exact e.map_source (hAs hx)
  let ψ:=chartPullback e (η:M→ℝ)
  have hψ:ContDiff ℝ ∞ ψ:=contDiff_chartPullback e he η.smooth η.hasCompactSupport hηtarget
  have hψc:HasCompactSupport ψ:=hasCompactSupport_chartPullback e η.hasCompactSupport hηtarget
  have hψs:tsupport ψ⊆nativeFiniteOuterOpenAnnulus a N:=by
    intro x hx
    obtain ⟨y,hy,rfl⟩:=tsupport_chartPullback_subset_image e η.hasCompactSupport hηtarget hx
    obtain ⟨z,hz,rfl⟩:=hη hy
    simpa only [e.left_inv (hAs hz)] using hz
  let φ:E→ℝ:=fun x=>ψ (a • x)
  have hφ:ContDiff ℝ ∞ φ:=hψ.comp (contDiff_id.const_smul a)
  have hφc:HasCompactSupport φ:=hψc.comp_homeomorph (Homeomorph.smulOfNeZero a ha.ne')
  have hφs:tsupport φ⊆{x:E|1<‖x‖}:=by
    intro x hx
    have hxψ:a • x∈tsupport ψ:=(tsupport_comp_eq_preimage ψ (Homeomorph.smulOfNeZero a ha.ne')).le hx
    have hn:a<‖a • x‖:=(hψs hxψ).1
    rw [norm_smul,Real.norm_of_nonneg ha.le] at hn
    change 1<‖x‖
    nlinarith only [ha,hn]
  have h0:(0:E)∉tsupport φ:=by
    intro hx
    have hh:=hφs hx
    norm_num at hh
  have hφval(y:E):φ (a⁻¹ • y)=ψ y:=by
    dsimp only [φ]
    rw [smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
  refine ⟨φ,hφ,hφc,h0,hφs,fun y hy=>?_,fun y hy=>?_⟩
  · exact (hφval y).trans (chartPullback_apply e (η:M→ℝ) (hKs hy))
  · exact (hφval y).trans (image_eq_zero_of_notMem_tsupport (fun h=>hy (hAK (hψs h))))

#print axioms exists_nativeFiniteOuter_smooth_test_adapter
end Yamabe3.Analysis.SpherePolar
