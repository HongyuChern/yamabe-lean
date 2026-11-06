import Yamabe3.Analysis.SmoothCompactSupportPreservingExtension
import Yamabe3.Analysis.NativeFiniteOuterTestAdapter

/-! Arbitrary native exterior tests have smooth compact Euclidean
exterior extensions agreeing on the whole retained chart ball. The
extension may extend beyond that ball; the actual field supplies the
compact support used in pairings. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Manifold Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

 theorem exists_nativeWholeExterior_smooth_test_adapter
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (R₀:ℝ) (hKs:closedBall (0:E) R₀⊆e.source)
    {a:ℝ} (ha:0<a) (η:EnergyTest g.leviCivitaData univ)
    (hη:tsupport (η:M→ℝ)⊆(e '' closedBall (0:E) a)ᶜ):
    ∃φ:E→ℝ,∃hφ:ContDiff ℝ ∞ φ,∃hc:HasCompactSupport φ,∃h0:(0:E)∉tsupport φ,
      tsupport φ⊆{x:E|1<‖x‖} ∧
      (∀y∈closedBall (0:E) R₀,φ (a⁻¹ • y)=η (e y)):=by
  have hT:ContDiffOn ℝ ∞ (fun x:E=>η (e x)) e.source:=by
    intro x hx
    exact (contMDiffAt_iff_contDiffAt.mp (η.smooth.contMDiffAt.comp x
      (he.contMDiffAt (e.open_source.mem_nhds hx)))).contDiffWithinAt
  obtain ⟨ψ,hψ,hψc,hψs,hψsupp,hgerm⟩:=exists_smooth_compact_support_preserving_extension
    e.open_source (isCompact_closedBall (0:E) R₀) hKs hT
  have hψouter:tsupport ψ⊆{x:E|a<‖x‖}:=by
    intro x hx
    by_contra! hn
    have hxball:x∈closedBall (0:E) a:=mem_closedBall_zero_iff.mpr (le_of_not_gt hn)
    have hnη:e x∉tsupport (η:M→ℝ):=by
      intro h
      exact hη h ⟨x,hxball,rfl⟩
    have heAt:ContinuousAt e x:=e.continuousOn.continuousAt (e.open_source.mem_nhds (hψs hx))
    have hz:(fun y:E=>η (e y))=ᶠ[𝓝 x](fun _=>0):=
      (notMem_tsupport_iff_eventuallyEq.mp hnη).comp_tendsto heAt
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) (hψsupp hx)
  let φ:E→ℝ:=fun x=>ψ (a • x)
  have hφ:ContDiff ℝ ∞ φ:=hψ.comp (contDiff_id.const_smul a)
  have hφc:HasCompactSupport φ:=hψc.comp_homeomorph (Homeomorph.smulOfNeZero a ha.ne')
  have hφs:tsupport φ⊆{x:E|1<‖x‖}:=by
    intro x hx
    have hxψ:a • x∈tsupport ψ:=(tsupport_comp_eq_preimage ψ (Homeomorph.smulOfNeZero a ha.ne')).le hx
    have hn:a<‖a • x‖:=hψouter hxψ
    rw [norm_smul,Real.norm_of_nonneg ha.le] at hn
    change 1<‖x‖
    nlinarith only [ha,hn]
  have h0:(0:E)∉tsupport φ:=by
    intro hx
    have hh:=hφs hx
    norm_num at hh
  refine ⟨φ,hφ,hφc,h0,hφs,?_⟩
  intro y hy
  change ψ (a • (a⁻¹ • y))=η (e y)
  rw [smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
  exact (hgerm y hy).self_of_nhds

#print axioms exists_nativeWholeExterior_smooth_test_adapter
end Yamabe3.Analysis.SpherePolar
