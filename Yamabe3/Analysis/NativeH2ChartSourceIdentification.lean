import Yamabe3.Analysis.NativeH2DensitySourceEquation
import Yamabe3.Analysis.NativeRestrictedChartAePullback
import Yamabe3.Analysis.NativeForcedSourceUniqueness

/-! The source of an actual native weak equation identifies the coordinate
H2 differential expression of the SAME volume representative. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

theorem nativeH2_chart_source_identification
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (hcoeff:∀x∈K,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    {O:Set E} (hO:IsOpen O) (hOc:IsCompact (closure O)) (hOK:closure O⊆K)
    (u:E→ℝ) (hum:Measurable u) (hu:MemWkp 2 2 u O)
    (W:H1Zero g.leviCivitaData univ) (F:Lp ℝ 2 g.volumeMeasure)
    (hrep:(toL2 g.leviCivitaData univ W:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' O)]
      nativeCompactChartFunction e (closure O) u)
    (hF:(W,F)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const (e '' O)):
    nativeWeakConformalDensity O gE u=ᵐ[volume.restrict O]
      (fun x=>gE.pullbackVolumeDensity id x*F (e x)):=by
  have hOs:O⊆e.source:=(subset_closure.trans hOK).trans hKs
  have hΩ:IsOpen (e '' O):=e.isOpen_image_of_subset_source hO hOs
  have hD:MemLp (nativeWeakConformalDensity O gE u) 2 (volume.restrict O):=
    nativeWeakConformalDensity_memLp hO hOc gE hu
  have hD0:MemLp (O.indicator (nativeWeakConformalDensity O gE u)) 2 volume:=
    (memLp_indicator_iff_restrict hO.measurableSet).mpr hD
  let G:=hD0.toLp (O.indicator (nativeWeakConformalDensity O gE u))
  have hGa:(G:E→ℝ)=ᵐ[volume]O.indicator (nativeWeakConformalDensity O gE u):=hD0.coeFn_toLp
  let H:=nativeDensityChartSourceCLM g gE e he hei hK hKs G
  have hHg:(W,H)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const (e '' O):=by
    apply nativeH2_chart_density_source_equation g gE e he hei hK hKs hcoeff hO hOc hOK u hum hu W G hrep
    filter_upwards [ae_restrict_of_ae (s:=O) hGa,ae_restrict_mem hO.measurableSet] with x hx hxO
    exact (hx.trans (indicator_of_mem hxO _)).symm
  have hHF:=nativeForcedEnergy_source_unique g (fun _:M=>0) contMDiff_const hΩ W H F hHg hF
  have hHrep:=nativeDensityChartSourceCLM_ae g gE e he hei hK hKs G
  have hvalue:(nativeDensityCorrectedChartSource gE e K (G:E→ℝ))=ᵐ[g.volumeMeasure.restrict (e '' O)](F:M→ℝ):=
    Filter.EventuallyEq.trans (Filter.EventuallyEq.symm (ae_restrict_of_ae (s:=e '' O) hHrep)) hHF
  have hp:=nativeRestrictedChart_ae_pullback g e he hei hK hKs hO.measurableSet
    (subset_closure.trans hOK) hΩ.measurableSet (subset_rfl:(e '' O)⊆e '' O) hvalue
  filter_upwards [hp,ae_restrict_of_ae (s:=O) hGa,ae_restrict_mem hO.measurableSet] with x hx hGx hxO
  have hxK:x∈K:=hOK (subset_closure hxO)
  rw [nativeDensityCorrectedChartSource,nativeCompactChartFunction,
    coordinateExtension_comp_apply e _ (hKs hxK),indicator_of_mem hxK] at hx
  rw [hGx,indicator_of_mem hxO] at hx
  exact (div_eq_iff ((native_density_smooth_positive gE).2 x).ne').mp hx |>.trans (mul_comm _ _)

#print axioms nativeH2_chart_source_identification
end Yamabe3.Analysis.SpherePolar
