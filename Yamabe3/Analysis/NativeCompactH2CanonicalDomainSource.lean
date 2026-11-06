import Yamabe3.Analysis.NativeCompactH2NativeDomainSource
import Yamabe3.Analysis.NativeGlobalH2ChartSourceCanonical

/-! Eliminate the auxiliary measurable representative without adding
an input. The compact H2 field, its actual source and its native
completion class are kept by volume a.e. identities. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Manifold Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.Weak
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

 theorem nativeCompactH2_canonical_domain_actual_source
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r R₀:ℝ} (hr:r<R₀) (hKs:closedBall (0:E) R₀⊆e.source)
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (u:E→ℝ) (hu:MemWkp 2 2 u univ)
    (hz:∀x:E,x∉closedBall (0:E) r→u x=0)
    (Ω:Set M) (hΩ:IsOpen Ω) (W:H1Zero g.leviCivitaData univ)
    (hrep:(toL2 g.leviCivitaData univ W:M→ℝ)=ᵐ[g.volumeMeasure.restrict Ω]coordinateExtension e u):
    ∃F_E:Lp ℝ 2 (volume:Measure E),
      (F_E:E→ℝ)=ᵐ[volume]nativeWeakConformalDensity univ gE u ∧
      (W,nativeDensityChartSourceCLM g gE e he hei (isCompact_closedBall (0:E) R₀) hKs F_E)∈
        nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const Ω:=by
  have hm:MemLp u 2 (volume:Measure E):=by simpa only [Measure.restrict_univ] using hu.memLp
  let v₀:E→ℝ:=hm.aestronglyMeasurable.mk u
  let v:E→ℝ:=(closedBall (0:E) r).indicator v₀
  have hvMeas:Measurable v:=hm.aestronglyMeasurable.stronglyMeasurable_mk.measurable.indicator measurableSet_closedBall
  have huv:u=ᵐ[volume]v:=by
    filter_upwards [hm.aestronglyMeasurable.ae_eq_mk] with x hx
    by_cases hxK:x∈closedBall (0:E) r
    · simpa only [v,indicator_of_mem hxK] using hx
    · simp only [v,indicator_of_notMem hxK,hz x hxK]
  have hv:MemWkp 2 2 v univ:=
    (MemWkp_congr_ae (by norm_num) isOpen_univ (by simpa only [Measure.restrict_univ] using huv)).mp hu
  have hvzero(x:E)(hx:x∉closedBall (0:E) r):v x=0:=indicator_of_notMem hx _
  have hnat:=coordinateExtension_congr_volume_ae g e he hei huv
  obtain ⟨F_E,hF,hforced⟩:=nativeCompactH2_native_domain_actual_source g gE e he hei hr hKs hcoeff
    v hvMeas hv hvzero Ω hΩ W (hrep.trans (ae_restrict_of_ae (s:=Ω) hnat))
  have hd:=nativeWeakConformalDensity_congr isOpen_univ gE
    (show u=ᵐ[volume.restrict univ]v by simpa only [Measure.restrict_univ] using huv)
  have hd':nativeWeakConformalDensity univ gE u=ᵐ[volume]nativeWeakConformalDensity univ gE v:=by
    simpa only [Measure.restrict_univ] using hd
  exact ⟨F_E,hF.trans hd'.symm,hforced⟩

#print axioms nativeCompactH2_canonical_domain_actual_source
end Yamabe3.Analysis.SpherePolar
