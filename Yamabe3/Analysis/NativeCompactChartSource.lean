import Yamabe3.Analysis.NativeCompactChartL2

/-! A coordinate L2 function restricted to a compact chart set produces
an actual native-volume L2 source, with its full pairing identity. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff Manifold RealInnerProductSpace
namespace Yamabe3.Analysis
open SpherePolar PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem memLp_nativeCompactChartFunction_of_restrict
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    {f:E→ℝ} (hf:Measurable f) (hf2:MemLp f 2 (volume.restrict K)) :
    MemLp (nativeCompactChartFunction e K f) 2 g.volumeMeasure := by
  have hh:=memLp_nativeCompactChartFunction g e he hei hK hKs
    (hf.indicator hK.measurableSet) ((memLp_indicator_iff_restrict hK.measurableSet).mpr hf2)
  simpa only [nativeCompactChartFunction,indicator_indicator,inter_self] using hh

theorem nativeCompactChartFunction_zero_off_image
    (e:OpenPartialHomeomorph E M) {K:Set E} (hKs:K⊆e.source) (f:E→ℝ)
    {y:M} (hy:y∉e '' K) : nativeCompactChartFunction e K f y=0 := by
  by_cases ht:y∈e.target
  · rw [nativeCompactChartFunction,coordinateExtension_apply e _ ht]
    apply indicator_of_notMem
    intro hk
    exact hy ⟨e.symm y,hk,e.right_inv ht⟩
  · exact indicator_of_notMem ht _

theorem integral_nativeCompactChartFunction_mul
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    {f:E→ℝ} (hf:Measurable f) {φ:M→ℝ} (hφ:Measurable φ) :
    (∫y,nativeCompactChartFunction e K f y*φ y ∂g.volumeMeasure)=
      ∫x in K,f x*φ (e x)*g.pullbackVolumeDensity e x := by
  calc
    _ = ∫y in e '' K,nativeCompactChartFunction e K f y*φ y ∂g.volumeMeasure := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      rw [nativeCompactChartFunction_zero_off_image e hKs f hy,zero_mul]
    _ = ∫x in K,nativeCompactChartFunction e K f (e x)*φ (e x)*g.pullbackVolumeDensity e x :=
      integral_compact_image_eq_pullback_density (g:=g) e he hei hK hKs
        ((measurable_coordinateExtension_of_measurable e (hf.indicator hK.measurableSet)).mul hφ)
    _ = _ := by
      apply setIntegral_congr_fun hK.measurableSet
      intro x hx
      dsimp only
      rw [nativeCompactChartFunction,coordinateExtension_comp_apply e _ (hKs hx),indicator_of_mem hx]

def nativeCompactChartSource
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    {f:E→ℝ} (hf:Measurable f) (hf2:MemLp f 2 (volume.restrict K)) : Lp ℝ 2 g.volumeMeasure :=
  (memLp_nativeCompactChartFunction_of_restrict g e he hei hK hKs hf hf2).toLp _

theorem nativeCompactChartSource_ae
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    {f:E→ℝ} (hf:Measurable f) (hf2:MemLp f 2 (volume.restrict K)) :
    (nativeCompactChartSource g e he hei hK hKs hf hf2:M→ℝ)=ᵐ[g.volumeMeasure] nativeCompactChartFunction e K f :=
  MemLp.coeFn_toLp _

theorem nativeCompactChartSource_pairing_test
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    {f:E→ℝ} (hf:Measurable f) (hf2:MemLp f 2 (volume.restrict K))
    (φ:EnergyTest g.leviCivitaData univ) :
    inner ℝ (nativeCompactChartSource g e he hei hK hKs hf hf2)
      (toL2 g.leviCivitaData univ (φ:H1Zero g.leviCivitaData univ))=
      ∫x in K,f x*φ (e x)*g.pullbackVolumeDensity e x := by
  rw [L2.inner_def,toL2_coe]
  trans ∫y,nativeCompactChartFunction e K f y*φ y ∂g.volumeMeasure
  · apply integral_congr_ae
    filter_upwards [nativeCompactChartSource_ae g e he hei hK hKs hf hf2,φ.memLp.coeFn_toLp] with y hy hφ
    simp only [Real.inner_apply,hy]
    change nativeCompactChartFunction e K f y*(φ.memLp.toLp φ) y=_
    rw [hφ]
  · exact integral_nativeCompactChartFunction_mul g e he hei hK hKs hf φ.smooth.continuous.measurable

#print axioms memLp_nativeCompactChartFunction_of_restrict
#print axioms integral_nativeCompactChartFunction_mul
#print axioms nativeCompactChartSource_ae
#print axioms nativeCompactChartSource_pairing_test
end Yamabe3.Analysis
