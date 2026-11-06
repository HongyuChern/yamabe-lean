import Yamabe3.Analysis.NativeChartLpTransport
import Yamabe3.Analysis.NativePhysicalShellCriticalTransport
import Yamabe3.Analysis.NativeOriginalSourceCriticalBound

/-! Actual density-corrected chart transport of one source. The cost is
on a fixed compact chart set, chosen before the source and physical scale. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

def nativeDensityCorrectedChartSource (gE:RiemannianMetric 3 E)
    (e:OpenPartialHomeomorph E M) (K:Set E) (f:E→ℝ) : M→ℝ :=
  nativeCompactChartFunction e K (fun x=>f x/(gE.pullbackVolumeDensity id x))

private theorem inverse_density_continuous (gE:RiemannianMetric 3 E) :
    Continuous (fun x:E=>(gE.pullbackVolumeDensity id x)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hh:=gE.contDiffAt_pullbackVolumeDensity (f:=id) (x:=x) contMDiffAt_id
    (by simpa using Function.injective_id)
  exact hh.1.continuousAt.inv₀ hh.2.ne'

theorem exists_nativeDensityCorrectedChart_lp_bound
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source) (p:ℝ≥0∞) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀f:E→ℝ,MemLp f p volume →
      MemLp (nativeDensityCorrectedChartSource gE e K f) p g.volumeMeasure ∧
      eLpNorm (nativeDensityCorrectedChartSource gE e K f) p g.volumeMeasure ≤ C*eLpNorm f p volume := by
  obtain ⟨D,hD⟩:=hK.exists_bound_of_continuousOn (inverse_density_continuous gE).continuousOn
  let J:=max D 0
  have hJ:0≤J := le_max_right _ _
  obtain ⟨N,hN,hn⟩:=exists_nativeCompactChart_lp_bound g e he hei hK hKs p
  refine ⟨N*ENNReal.ofReal J,by finiteness,fun f hf=>?_⟩
  have hi:MemLp (fun x:E=>(gE.pullbackVolumeDensity id x)⁻¹) ⊤ (volume.restrict K) :=
    continuousOn_compact_memLp_top hK (inverse_density_continuous gE).continuousOn
  have hmul:MemLp (fun x:E=>f x/(gE.pullbackVolumeDensity id x)) p (volume.restrict K) := by
    apply ((hf.restrict K).mul' hi).ae_eq
    exact Eventually.of_forall fun x=>by dsimp only;ring
  let F:=K.indicator (fun x:E=>f x/(gE.pullbackVolumeDensity id x))
  have hF:MemLp F p volume := (memLp_indicator_iff_restrict hK.measurableSet).mpr hmul
  have hnorm:eLpNorm F p volume ≤ ENNReal.ofReal J*eLpNorm f p volume := by
    rw [show F=K.indicator (fun x:E=>f x/(gE.pullbackVolumeDensity id x)) from rfl,
      eLpNorm_indicator_eq_eLpNorm_restrict hK.measurableSet]
    have hb:eLpNorm (fun x:E=>f x/(gE.pullbackVolumeDensity id x)) p (volume.restrict K) ≤
        eLpNorm (J • f) p (volume.restrict K) := by
      apply eLpNorm_mono_ae
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      rw [div_eq_mul_inv,norm_mul,Pi.smul_apply,norm_smul,Real.norm_of_nonneg hJ]
      exact (mul_le_mul_of_nonneg_left ((hD x hx).trans (le_max_left _ _)) (norm_nonneg _)).trans_eq (by ring)
    rw [eLpNorm_const_smul,Real.enorm_eq_ofReal hJ] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (eLpNorm_mono_measure f Measure.restrict_le_self) zero_le)
  have hh:=hn F hF
  have hid:nativeCompactChartFunction e K F=nativeDensityCorrectedChartSource gE e K f := by
    simp only [nativeCompactChartFunction,F,indicator_indicator,inter_self,nativeDensityCorrectedChartSource]
  rw [hid] at hh
  exact ⟨hh.1,hh.2.trans ((mul_le_mul_of_nonneg_left hnorm zero_le).trans_eq (by ring))⟩

theorem exists_nativePhysicalShellSource_critical_bound
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀a:ℝ,0<a → ∀s:ℝ,∀U:NativeCollarL2,
      MemLp (nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a s U)) 2 g.volumeMeasure ∧
      MemLp (nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a s U)) (6/5:ℝ≥0∞) g.volumeMeasure ∧
      eLpNorm (nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a s U)) (6/5:ℝ≥0∞) g.volumeMeasure ≤
        C*ENNReal.ofReal (Real.sqrt a*Real.exp (-2*s)*‖U‖) := by
  obtain ⟨D,hD,hd⟩:=exists_nativeDensityCorrectedChart_lp_bound g gE e he hei hK hKs (6/5:ℝ≥0∞)
  obtain ⟨J,hJ,hj⟩:=exists_nativeDensityCorrectedChart_lp_bound g gE e he hei hK hKs 2
  refine ⟨D*ENNReal.ofReal (8*nativeSourceShellCriticalCost),by finiteness,fun a ha s U=>?_⟩
  have hsrc:=nativePhysicalShellSource_critical_bound ha s U
  have hc:=hd _ hsrc.1
  refine ⟨(hj _ (nativePhysicalShellSource_memLp_two a s U)).1,hc.1,?_⟩
  apply (hc.2.trans (mul_le_mul_of_nonneg_left hsrc.2 zero_le)).trans_eq
  rw [mul_assoc D,←ENNReal.ofReal_mul (mul_nonneg (by norm_num) ENNReal.toReal_nonneg:0≤8*nativeSourceShellCriticalCost)]
  congr 2
  ring

#print axioms exists_nativeDensityCorrectedChart_lp_bound
#print axioms exists_nativePhysicalShellSource_critical_bound
end Yamabe3.Analysis.SpherePolar
