import Yamabe3.Analysis.NativeRestrictedChartAeTransport
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.L2Pullback

/-! Retained-volume a.e. identities pull back on actual coordinate domains.
This uses positive chart density on compact sets, never restriction to a sphere. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology
namespace Yamabe3.Analysis.SpherePolar
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem nativeRestrictedChart_ae_pullback
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    {D:Set E} (hD:MeasurableSet D) (hDK:D⊆K)
    {Ω:Set M} (hΩ:MeasurableSet Ω) (hDΩ:e '' D⊆Ω)
    {f h:M→ℝ} (hfh:f=ᵐ[g.volumeMeasure.restrict Ω]h):
    (fun x=>f (e x))=ᵐ[volume.restrict D](fun x=>h (e x)):=by
  classical
  have hz:(Ω.indicator f)=ᵐ[g.volumeMeasure](Ω.indicator h):=by
    filter_upwards [(ae_restrict_iff' hΩ).mp hfh] with y hy
    by_cases hyΩ:y∈Ω
    · rw [indicator_of_mem hyΩ,indicator_of_mem hyΩ,hy hyΩ]
    · rw [indicator_of_notMem hyΩ,indicator_of_notMem hyΩ]
  have hp:=g.ae_comp_on_compact e he hei hK hKs hz
  have hr:=ae_mono (Measure.restrict_mono hDK le_rfl) hp
  filter_upwards [hr,ae_restrict_mem hD] with x hx hxD
  have hxΩ:e x∈Ω:=hDΩ ⟨x,hxD,rfl⟩
  simpa only [indicator_of_mem hxΩ] using hx

#print axioms nativeRestrictedChart_ae_pullback
end Yamabe3.Analysis.SpherePolar
