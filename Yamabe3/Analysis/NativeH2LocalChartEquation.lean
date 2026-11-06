import Yamabe3.Analysis.NativeH2DensitySourceEquation
import Yamabe3.Analysis.NativeForcedEnergyLocality

/-! A local H2 coordinate producer with a COMMON density-corrected source
class gives the native weak equation on the entire chart domain. Compact
neighbourhoods and the finite native test partition are constructed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

theorem nativeH2local_chart_density_source_equation
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (hcoeff:∀x∈K,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    {O:Set E} (hO:IsOpen O) (hOK:O⊆K)
    (u:E→ℝ) (hum:Measurable u) (W:H1Zero g.leviCivitaData univ)
    (F_E:Lp ℝ 2 (volume:Measure E))
    (hrep:(toL2 g.leviCivitaData univ W:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' O)]
      coordinateExtension e u)
    (hsource:∀U:Set E,IsOpen U →IsCompact (closure U) →closure U⊆O →
      MemWkp 2 2 u U ∧ nativeWeakConformalDensity U gE u=ᵐ[volume.restrict U](F_E:E→ℝ)):
    (W,nativeDensityChartSourceCLM g gE e he hei hK hKs F_E)∈
      nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const (e '' O):=by
  apply nativeForcedEnergySpace_of_local
  rintro y ⟨x,hx,rfl⟩
  obtain ⟨r,hr,hball⟩:=Metric.isOpen_iff.mp hO x hx
  let U:=ball x (r/2)
  have hUc:IsCompact (closure U):=by
    dsimp only [U]
    rw [closure_ball x (by positivity:r/2≠0)]
    exact isCompact_closedBall _ _
  have hUO:closure U⊆O:=closure_ball_subset_closedBall.trans
    ((closedBall_subset_ball (by linarith:r/2<r)).trans hball)
  have hUs:U⊆e.source:=(subset_closure.trans hUO).trans (hOK.trans hKs)
  have hΩ:IsOpen (e '' U):=e.isOpen_image_of_subset_source isOpen_ball hUs
  refine ⟨e '' U,hΩ,⟨x,mem_ball_self (by positivity:r/2>0),rfl⟩,?_⟩
  obtain ⟨hu,hs⟩:=hsource U isOpen_ball hUc hUO
  apply nativeH2_chart_density_source_equation g gE e he hei hK hKs hcoeff
    isOpen_ball hUc (hUO.trans hOK) u hum hu W F_E ?_ hs
  have hr: (toL2 g.leviCivitaData univ W:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' U)]
      coordinateExtension e u:=
    ae_mono (Measure.restrict_mono (image_mono (subset_closure.trans hUO)) le_rfl) hrep
  filter_upwards [hr,ae_restrict_mem hΩ.measurableSet] with y hy hyU
  obtain ⟨z,hz,rfl⟩:=hyU
  rw [hy,nativeCompactChartFunction,coordinateExtension_comp_apply e _ (hUs hz),
    coordinateExtension_comp_apply e _ (hUs hz),indicator_of_mem (subset_closure hz)]

#print axioms nativeH2local_chart_density_source_equation
end Yamabe3.Analysis.SpherePolar
