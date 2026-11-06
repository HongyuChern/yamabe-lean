import Yamabe3.Analysis.NativeH2DensitySourceEquation
import Yamabe3.Analysis.NativeRestrictedChartAeTransport
import Yamabe3.Analysis.WeakLaplacianDilation

/-! Local H2 of the SAME native volume representative produces a
local L2 source. No source equation is supplied as an input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

theorem memWkpLocally_comp_dilation {O:Set E} {u:E→ℝ} {r:ℝ} (hr:r≠0) {k:ℕ}
    (hu:MemWkpLocally k u O):
    MemWkpLocally k (fun x:E=>u (r • x)) ((fun x:E=>r • x) ⁻¹' O):=by
  intro x hx
  obtain ⟨U,hU,hxU,hUO,huU⟩:=hu (r • x) hx
  refine ⟨(fun x:E=>r • x) ⁻¹' U,hU.preimage (continuous_const_smul r),hxU,preimage_mono hUO,?_⟩
  exact memWkp_comp_dilation hr hU (by norm_num) k huU

variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

theorem nativeLocalH2_chart_source
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (hcoeff:∀x∈K,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    {D:Set E} (hD:IsOpen D) (hDK:D⊆K)
    (u:E→ℝ) (hum:Measurable u) (hu:MemWkpLocally 2 u D)
    (W:H1Zero g.leviCivitaData univ)
    (hrep:(toL2 g.leviCivitaData univ W:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' D)]coordinateExtension e u):
    ∀y∈e '' D,∃U:Set M,IsOpen U ∧ y∈U ∧ U⊆e '' D ∧
      ∃F:Lp ℝ 2 g.volumeMeasure,(W,F)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const U:=by
  rintro y ⟨x,hx,rfl⟩
  obtain ⟨r,hr,hrD⟩:=Metric.isOpen_iff.mp hD x hx
  let O:=ball x (r/2)
  have hO:IsOpen O:=isOpen_ball
  have hOc:IsCompact (closure O):=by
    dsimp only [O]
    rw [closure_ball _ (by positivity:r/2≠0)]
    exact isCompact_closedBall _ _
  have hOD:closure O⊆D:=closure_ball_subset_closedBall.trans
    ((closedBall_subset_ball (by linarith:r/2<r)).trans hrD)
  have hOK:closure O⊆K:=hOD.trans hDK
  have hOs:O⊆e.source:=(subset_closure.trans hOK).trans hKs
  have huO:MemWkp 2 2 u O:=memWkp_on_precompact_of_locally hu hO hOc hOD
  have hDensity:MemLp (nativeWeakConformalDensity O gE u) 2 (volume.restrict O):=
    nativeWeakConformalDensity_memLp hO hOc gE huO
  have hG:MemLp (O.indicator (nativeWeakConformalDensity O gE u)) 2 volume:=
    (memLp_indicator_iff_restrict hO.measurableSet).mpr hDensity
  let G:=hG.toLp (O.indicator (nativeWeakConformalDensity O gE u))
  have hGa:(G:E→ℝ)=ᵐ[volume]O.indicator (nativeWeakConformalDensity O gE u):=hG.coeFn_toLp
  let F:=nativeDensityChartSourceCLM g gE e he hei hK hKs G
  refine ⟨e '' O,e.isOpen_image_of_subset_source hO hOs,⟨x,mem_ball_self (by positivity),rfl⟩,
    image_mono (subset_closure.trans hOD),F,?_⟩
  apply nativeH2_chart_density_source_equation g gE e he hei hK hKs hcoeff hO hOc hOK u hum huO W G
  · have hs:(toL2 g.leviCivitaData univ W:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' O)]coordinateExtension e u:=
      ae_mono (Measure.restrict_mono (image_mono (subset_closure.trans hOD)) le_rfl) hrep
    filter_upwards [hs,ae_restrict_mem (e.isOpen_image_of_subset_source hO hOs).measurableSet] with z hz hzO
    obtain ⟨t,ht,rfl⟩:=hzO
    rw [hz,nativeCompactChartFunction,coordinateExtension_comp_apply e _ (hOs ht),
      coordinateExtension_comp_apply e _ (hOs ht),indicator_of_mem (subset_closure ht)]
  · filter_upwards [ae_restrict_of_ae (s:=O) hGa,ae_restrict_mem hO.measurableSet] with z hz hzO
    exact (hz.trans (indicator_of_mem hzO _)).symm

#print axioms memWkpLocally_comp_dilation
#print axioms nativeLocalH2_chart_source
end Yamabe3.Analysis.SpherePolar
