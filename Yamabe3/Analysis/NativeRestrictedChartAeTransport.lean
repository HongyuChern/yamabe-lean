import Yamabe3.Analysis.NativeChartAeTransport

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

theorem coordinateExtension_congr_restricted_volume_ae
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O:Set E} (hO:IsOpen O) (hOs:O⊆e.source)
    {f h:E→ℝ} (hfh:f=ᵐ[volume.restrict O]h):
    coordinateExtension e f=ᵐ[g.volumeMeasure.restrict (e '' O)]coordinateExtension e h:=by
  have hh:=nativeCompactChart_congr_volume_ae g e he hei hO.measurableSet hfh
  have hΩ:IsOpen (e '' O):=e.isOpen_image_of_subset_source hO hOs
  filter_upwards [ae_restrict_of_ae (s:=e '' O) hh,ae_restrict_mem hΩ.measurableSet] with y hy hyO
  obtain ⟨x,hx,rfl⟩:=hyO
  simpa only [nativeCompactChartFunction,coordinateExtension_comp_apply e _ (hOs hx),indicator_of_mem hx] using hy

#print axioms coordinateExtension_congr_restricted_volume_ae
end Yamabe3.Analysis.SpherePolar
