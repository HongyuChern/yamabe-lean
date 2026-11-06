import Yamabe3.Analysis.NativeC1CompactEnergyApproximation
import Yamabe3.Analysis.NativePhysicalCanonicalSphereTrace

/-! An actual native H1 lifting of compact C1 coordinate data, with the
literal value trace of that same function. Both energy and trace limits
come from one smooth approximation. No infinite smoothness is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT UniformSpace
open scoped Topology ContDiff ENNReal RealInnerProductSpace Manifold
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet UniformElliptic
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
local notation "D" => nativeWeakEuclideanD

theorem exists_native_C1_chart_energy_with_trace
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O K:Set E} (hO:IsOpen O) (hK:IsCompact K) (hKs:K⊆e.source) (hOK:O⊆K)
    {u:E→ℝ} (hu:ContDiff ℝ 1 u) (hc:HasCompactSupport u) (hs:tsupport u⊆O)
    {a b r:ℝ} (ha:0<a) (hab:a<b) (hr:r∈Icc a b)
    (hKO:sphereTraceAnnulus a b⊆O) :
    ∃z:H1Zero g.leviCivitaData univ,
      (toL2 g.leviCivitaData univ z:M→ℝ)=ᵐ[g.volumeMeasure] coordinateExtension e u ∧
      (nativeSphereTraceCLM g e he hei ha hab hr (hKO.trans (hOK.trans hKs)) z:S→ℝ)=ᵐ[angularVolume]
        (fun θ:S=>u (r • (θ:E))) := by
  classical
  obtain ⟨zE,φ,hzE,hφlim,htrace⟩:=exists_native_C1_compact_energy_approximation hO hu hc hs
  let I:=nativeDomainEnergyInclusion g (e '' O)
  let C:=nativeWeakChartH1CLM g e he hei hK hKs hOK
  let z:=I (C zE)
  let T:=nativeSphereTraceCLM g e he hei ha hab hr (hKO.trans (hOK.trans hKs))
  have hmask:O.indicator u=u := by
    funext x
    by_cases hx:x∈O
    · exact indicator_of_mem hx u
    · rw [indicator_of_notMem hx,image_eq_zero_of_notMem_tsupport (fun ht=>hx (hs ht))]
  have hzEu:(toL2 D O zE:E→ℝ)=ᵐ[volume] u := by simpa only [hmask] using hzE
  have hml:MemLp (toL2 D O zE:E→ℝ) 2 volume := by
    simpa only [native_euclideanMetric_volumeMeasure] using Lp.memLp (toL2 D O zE)
  have hum:MemLp u 2 volume:=hu.continuous.memLp_of_hasCompactSupport hc
  have hae:=nativeCompactChartFunction_congr_ae g e he hei hK hKs
    (Lp.stronglyMeasurable (toL2 D O zE)).measurable hu.continuous.measurable hml hum hzEu
  rw [nativeCompactChartFunction_eq_of_tsupport_subset e (hs.trans hOK)] at hae
  have hz:(toL2 g.leviCivitaData univ z:M→ℝ)=ᵐ[g.volumeMeasure] coordinateExtension e u := by
    dsimp only [z,I,C]
    rw [nativeDomainEnergyInclusion_toL2,toL2_nativeWeakChartH1CLM]
    exact (nativeCompactChartL2Linear_ae g e he hei hK hKs (toL2 D O zE)).trans hae
  refine ⟨z,hz,?_⟩
  have hTlim:Tendsto (fun n=>T (I (C (φ n:H1Zero D O)))) atTop (𝓝 (T z)) :=
    T.continuous.continuousAt.tendsto.comp (I.continuous.continuousAt.tendsto.comp
      (C.continuous.continuousAt.tendsto.comp hφlim))
  have hrad:Continuous (fun θ:S=>r • (θ:E)):=by fun_prop
  let htm(n:ℕ):MemLp (fun θ:S=>φ n (r • (θ:E))) 2 angularVolume:=
    (((φ n).smooth.contDiff.continuous).comp hrad).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let humt:MemLp (fun θ:S=>u (r • (θ:E))) 2 angularVolume:=
    (hu.continuous.comp hrad).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTeq(n:ℕ):T (I (C (φ n:H1Zero D O)))=(htm n).toLp (fun θ:S=>φ n (r • (θ:E))) := by
    dsimp only [T,I,C]
    rw [nativeWeakChartH1CLM_coe,nativeDomainEnergyInclusion_coe,nativeSphereTraceCLM_coe]
    apply Lp.ext
    have h:=nativeSphereTestTraceLinear_ae g e r
      (fun θ=>(hKO.trans (hOK.trans hKs)) (radial_mem_sphereTraceAnnulus ha hr θ))
      (nativeDomainTestInclusion g (e '' O) (nativeWeakChartTest g e hei (hOK.trans hKs) (φ n)))
    filter_upwards [h,(htm n).coeFn_toLp] with θ hθ huθ
    rw [huθ]
    exact hθ.trans (coordinateExtension_comp_apply e _
      ((hKO.trans (hOK.trans hKs)) (radial_mem_sphereTraceAnnulus ha hr θ)))
  have hother:=native_tendsto_toLp_of_integral_sq_sub htm humt (htrace a b r ha hab hr hKO)
  have heq:T z=humt.toLp (fun θ:S=>u (r • (θ:E))) :=
    tendsto_nhds_unique (by simpa only [hTeq] using hTlim) hother
  rw [heq]
  exact humt.coeFn_toLp

#print axioms exists_native_C1_chart_energy_with_trace
end Yamabe3.Analysis.SpherePolar
