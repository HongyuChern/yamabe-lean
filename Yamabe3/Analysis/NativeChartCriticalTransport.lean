import Yamabe3.Analysis.NativeCompactChartL2
import Yamabe3.Analysis.NativeSixFifthsForcing

/-! Genuine critical source transport through the retained chart and
volume density. The density cost is proved on one fixed compact set;
no Euclidean norm is silently used as a native source norm. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem nativeChart_memLp_norm_of_density
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {p:ℝ≥0∞} {f:E→ℝ}
    (hf:MemLp f p ((volume.withDensity (fun x=>ENNReal.ofReal (g.pullbackVolumeDensity e x))).restrict e.source)) :
    MemLp (coordinateExtension e f) p g.volumeMeasure ∧
    eLpNorm (coordinateExtension e f) p g.volumeMeasure=
      eLpNorm f p ((volume.withDensity (fun x=>ENNReal.ofReal (g.pullbackVolumeDensity e x))).restrict e.source) := by
  rw [←g.map_restrict_volumeMeasure_symm e he hei] at hf ⊢
  have hm:AEMeasurable e.symm (g.volumeMeasure.restrict e.target):=
    e.symm.continuousOn.aemeasurable e.open_target.measurableSet
  have hp:=hf.comp_of_map hm
  have hae:(f ∘ e.symm)=ᵐ[g.volumeMeasure.restrict e.target]coordinateExtension e f:=by
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
    exact (coordinateExtension_apply e f hy).symm
  have ht:MemLp (coordinateExtension e f) p (g.volumeMeasure.restrict e.target):=hp.ae_eq hae
  have hi:MemLp (e.target.indicator (coordinateExtension e f)) p g.volumeMeasure:=
    (memLp_indicator_iff_restrict e.open_target.measurableSet).mpr ht
  have hid:e.target.indicator (coordinateExtension e f)=coordinateExtension e f:=by
    ext y
    by_cases hy:y∈e.target
    · exact indicator_of_mem hy _
    · simp only [coordinateExtension,indicator_of_notMem hy]
  refine ⟨hid ▸ hi,?_⟩
  rw [←hid,eLpNorm_indicator_eq_eLpNorm_restrict e.open_target.measurableSet]
  exact (eLpNorm_congr_ae hae).symm.trans (eLpNorm_map_measure hf.1 hm).symm

theorem exists_nativeCompactChart_critical_bound
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀f:E→ℝ,MemLp f (6/5:ℝ≥0∞) volume→
      MemLp (nativeCompactChartFunction e K f) (6/5:ℝ≥0∞) g.volumeMeasure ∧
      eLpNorm (nativeCompactChartFunction e K f) (6/5:ℝ≥0∞) g.volumeMeasure≤C*eLpNorm f (6/5:ℝ≥0∞) volume := by
  obtain ⟨B,hB,hρ⟩:=exists_nativeCompactChartDensity_bound g e he hei hK hKs
  let ρ:=fun x:E=>ENNReal.ofReal (g.pullbackVolumeDensity e x)
  have hle:(volume.restrict K).withDensity ρ≤ENNReal.ofReal B • (volume.restrict K):=by
    have hh:ρ≤ᵐ[volume.restrict K]fun _=>ENNReal.ofReal B:=by
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hρ x hx))
    simpa only [withDensity_const] using withDensity_mono hh
  let C:ℝ≥0∞:=(ENNReal.ofReal B)^((1/(6/5:ℝ≥0∞)).toReal)
  refine ⟨C,ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top,fun f hf=>?_⟩
  have hfk:MemLp f (6/5:ℝ≥0∞) ((volume.restrict K).withDensity ρ):=
    (hf.restrict K).of_measure_le_smul ENNReal.ofReal_ne_top hle
  have hμ:((volume.withDensity ρ).restrict e.source).restrict K=(volume.restrict K).withDensity ρ:=by
    rw [Measure.restrict_restrict hK.measurableSet,inter_eq_left.mpr hKs,
      restrict_withDensity hK.measurableSet]
  have hfH:MemLp (K.indicator f) (6/5:ℝ≥0∞) ((volume.withDensity ρ).restrict e.source):=by
    apply (memLp_indicator_iff_restrict hK.measurableSet).mpr
    rw [hμ]
    exact hfk
  have hh:=nativeChart_memLp_norm_of_density g e he hei hfH
  refine ⟨hh.1,hh.2.le.trans ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hK.measurableSet,hμ]
  exact (eLpNorm_le_of_measure_le_smul hle).trans
    (mul_le_mul le_rfl (eLpNorm_mono_measure f (Measure.restrict_le_self)) zero_le zero_le)

#print axioms nativeChart_memLp_norm_of_density
#print axioms exists_nativeCompactChart_critical_bound
end Yamabe3.Analysis.SpherePolar
