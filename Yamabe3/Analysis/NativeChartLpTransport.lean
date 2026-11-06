import Yamabe3.Analysis.NativeChartCriticalTransport

/-! The compact-chart density transport bound for arbitrary Lp
exponents. This pays the actual native measure cost for the bubble tail. -/
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

theorem exists_nativeCompactChart_lp_bound
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source) (p:ℝ≥0∞) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀f:E→ℝ,MemLp f p volume→
      MemLp (nativeCompactChartFunction e K f) p g.volumeMeasure ∧
      eLpNorm (nativeCompactChartFunction e K f) p g.volumeMeasure≤C*eLpNorm f p volume := by
  obtain ⟨B,hB,hρ⟩:=exists_nativeCompactChartDensity_bound g e he hei hK hKs
  let ρ:=fun x:E=>ENNReal.ofReal (g.pullbackVolumeDensity e x)
  have hle:(volume.restrict K).withDensity ρ≤ENNReal.ofReal B • (volume.restrict K):=by
    have hh:ρ≤ᵐ[volume.restrict K]fun _=>ENNReal.ofReal B:=by
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hρ x hx))
    simpa only [withDensity_const] using withDensity_mono hh
  let C:ℝ≥0∞:=(ENNReal.ofReal B)^((1/p).toReal)
  refine ⟨C,ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top,fun f hf=>?_⟩
  have hfk:MemLp f p ((volume.restrict K).withDensity ρ):=
    (hf.restrict K).of_measure_le_smul ENNReal.ofReal_ne_top hle
  have hμ:((volume.withDensity ρ).restrict e.source).restrict K=(volume.restrict K).withDensity ρ:=by
    rw [Measure.restrict_restrict hK.measurableSet,inter_eq_left.mpr hKs,
      restrict_withDensity hK.measurableSet]
  have hfH:MemLp (K.indicator f) p ((volume.withDensity ρ).restrict e.source):=by
    apply (memLp_indicator_iff_restrict hK.measurableSet).mpr
    rw [hμ]
    exact hfk
  have hh:=nativeChart_memLp_norm_of_density g e he hei hfH
  refine ⟨hh.1,hh.2.le.trans ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hK.measurableSet,hμ]
  exact (eLpNorm_le_of_measure_le_smul hle).trans
    (mul_le_mul le_rfl (eLpNorm_mono_measure f (Measure.restrict_le_self)) zero_le zero_le)


#print axioms exists_nativeCompactChart_lp_bound
end Yamabe3.Analysis.SpherePolar
