import Yamabe3.Analysis.NativeChartCriticalTransport

/-! Native-volume transport of a coordinate a.e. identity. No restriction
of a volume identity to a hypersurface and no L2 hypothesis is used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem coordinateExtension_congr_volume_ae
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {f h:E→ℝ} (hfh:f=ᵐ[volume]h) :
    coordinateExtension e f=ᵐ[g.volumeMeasure]coordinateExtension e h := by
  have hd:f=ᵐ[volume.withDensity (fun x=>ENNReal.ofReal (g.pullbackVolumeDensity e x))]h :=
    (withDensity_absolutelyContinuous volume _).ae_eq hfh
  have hs:=ae_restrict_of_ae (s:=e.source) hd
  rw [←g.map_restrict_volumeMeasure_symm e he hei] at hs
  have hm:AEMeasurable e.symm (g.volumeMeasure.restrict e.target) :=
    e.symm.continuousOn.aemeasurable e.open_target.measurableSet
  have hh:(f ∘ e.symm)=ᵐ[g.volumeMeasure.restrict e.target](h ∘ e.symm) := ae_eq_comp hm hs
  filter_upwards [(ae_restrict_iff' e.open_target.measurableSet).mp hh] with y hy
  by_cases ht:y∈e.target
  · rw [coordinateExtension_apply e f ht,coordinateExtension_apply e h ht]
    exact hy ht
  · simp only [coordinateExtension,indicator_of_notMem ht]

theorem nativeCompactChart_congr_volume_ae
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:MeasurableSet K) {f h:E→ℝ}
    (hfh:f=ᵐ[volume.restrict K]h) :
    nativeCompactChartFunction e K f=ᵐ[g.volumeMeasure]nativeCompactChartFunction e K h := by
  apply coordinateExtension_congr_volume_ae g e he hei
  filter_upwards [(ae_restrict_iff' hK).mp hfh] with x hx
  by_cases hk:x∈K
  · simp only [indicator_of_mem hk,hx hk]
  · simp only [indicator_of_notMem hk]

#print axioms coordinateExtension_congr_volume_ae
#print axioms nativeCompactChart_congr_volume_ae
end Yamabe3.Analysis.SpherePolar
