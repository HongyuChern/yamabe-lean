import Yamabe3.Analysis.NativeGlobalH2ConformalScaling
import Yamabe3.Analysis.NativeH2LocalChartEquation

/-! A genuine global H2 coordinate field produces its own actual
native L2 source on a compact chart. No weak PDE or inverse is an input.
The representation premise is explicit and must be discharged by the
actual completed-field producer before applying this local interface. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Manifold Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.Weak
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

 theorem nativeGlobalH2_chart_actual_density_source
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (R₀:ℝ) (hKs:closedBall (0:E) R₀⊆e.source)
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    {O:Set E} (hO:IsOpen O) (hOK:O⊆closedBall (0:E) R₀)
    (u:E→ℝ) (hum:Measurable u) (hu:MemWkp 2 2 u univ)
    (W:H1Zero g.leviCivitaData univ)
    (hrep:(toL2 g.leviCivitaData univ W:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' O)]coordinateExtension e u):
    ∃F_E:Lp ℝ 2 (volume:Measure E),
      (F_E:E→ℝ)=ᵐ[volume]((closedBall (0:E) R₀).indicator
        (nativeWeakConformalDensity (ball (0:E) (R₀+1)) gE u)) ∧
      (W,nativeDensityChartSourceCLM g gE e he hei (isCompact_closedBall (0:E) R₀) hKs F_E)∈
        nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const (e '' O):=by
  let K:=closedBall (0:E) R₀
  let B:=ball (0:E) (R₀+1)
  have hKB:K⊆B:=by
    intro x hx
    apply mem_ball_zero_iff.mpr
    exact lt_of_le_of_lt (mem_closedBall_zero_iff.mp hx) (by linarith)
  have hBc:IsCompact (closure B):=Metric.isCompact_of_isClosed_isBounded isClosed_closure
    ((Metric.isBounded_ball (x:=(0:E)) (r:=R₀+1)).closure)
  have huB:MemWkp 2 2 u B:=hu.mono_set (by norm_num) isOpen_ball (subset_univ _)
  have hRaw:MemLp (nativeWeakConformalDensity B gE u) 2 (volume.restrict K):=
    (nativeWeakConformalDensity_memLp isOpen_ball hBc gE huB).mono_measure (Measure.restrict_mono hKB le_rfl)
  have hF:MemLp (K.indicator (nativeWeakConformalDensity B gE u)) 2 volume:=
    (memLp_indicator_iff_restrict measurableSet_closedBall).mpr hRaw
  let F_E:=hF.toLp (K.indicator (nativeWeakConformalDensity B gE u))
  have hFa:(F_E:E→ℝ)=ᵐ[volume](K.indicator (nativeWeakConformalDensity B gE u)):=hF.coeFn_toLp
  refine ⟨F_E,hFa,?_⟩
  apply nativeH2local_chart_density_source_equation g gE e he hei (isCompact_closedBall (0:E) R₀) hKs hcoeff
    hO hOK u hum W F_E hrep
  intro U hU hUc hUO
  have hUK:U⊆K:=subset_closure.trans (hUO.trans hOK)
  have hUB:U⊆B:=hUK.trans hKB
  refine ⟨hu.mono_set (by norm_num) hU (subset_univ _),?_⟩
  have hm:=nativeWeakConformalDensity_mono hU hUB huB gE
  filter_upwards [hm,ae_restrict_of_ae (s:=U) hFa,ae_restrict_mem hU.measurableSet] with x hx hf hxU
  rw [hf,indicator_of_mem (hUK hxU)]
  exact hx.symm

#print axioms nativeGlobalH2_chart_actual_density_source
end Yamabe3.Analysis.SpherePolar
