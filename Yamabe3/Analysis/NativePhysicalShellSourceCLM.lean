import Yamabe3.Analysis.NativeDensityCorrectedChartLp
import Yamabe3.Analysis.NativeChartAeTransport
import Yamabe3.Analysis.WeakLaplacianDilation

/-! One actual physical shell source gives a bounded linear native
critical source. Its native L2 and critical classes have the SAME source
representative; density, shell, factor eight and exact dilation persist. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ENNReal Manifold ContDiff
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
private instance shellCritical_ge_one:Fact (1≤(6/5:ℝ≥0∞)) := ⟨one_le_sixFifths⟩

private theorem zeroShell_add_ae (U W:NativeCollarL2) :
    nativeZeroShellSource (U+W)=ᵐ[volume](nativeZeroShellSource U+nativeZeroShellSource W) := by
  have h:=ae_mono (Measure.restrict_mono nativeSourceShell_subset_collar le_rfl) (Lp.coeFn_add U W)
  filter_upwards [(ae_restrict_iff' nativeSourceShell_measurable).mp h] with x hx
  by_cases hs:x∈nativeSourceShell
  · simpa only [nativeZeroShellSource,Pi.add_apply,indicator_of_mem hs] using hx hs
  · simp only [nativeZeroShellSource,Pi.add_apply,indicator_of_notMem hs,add_zero]

private theorem zeroShell_smul_ae (c:ℝ) (U:NativeCollarL2) :
    nativeZeroShellSource (c • U)=ᵐ[volume](c • nativeZeroShellSource U) := by
  have h:=ae_mono (Measure.restrict_mono nativeSourceShell_subset_collar le_rfl) (Lp.coeFn_smul c U)
  filter_upwards [(ae_restrict_iff' nativeSourceShell_measurable).mp h] with x hx
  by_cases hs:x∈nativeSourceShell
  · simpa only [nativeZeroShellSource,Pi.smul_apply,indicator_of_mem hs] using hx hs
  · simp only [nativeZeroShellSource,Pi.smul_apply,indicator_of_notMem hs,smul_zero]

theorem nativePhysicalShellSource_add_ae (a s:ℝ) (U W:NativeCollarL2) :
    nativePhysicalShellSource a s (U+W)=ᵐ[volume]
      (nativePhysicalShellSource a s U+nativePhysicalShellSource a s W) := by
  have h:=ae_comp_dilation (Real.exp_ne_zero (s-Real.log a))
    (ae_restrict_of_ae (s:=univ) (zeroShell_add_ae U W))
  simp only [preimage_univ,Measure.restrict_univ] at h
  filter_upwards [h] with x hx
  simp only [nativePhysicalShellSource,Pi.add_apply] at hx ⊢
  rw [hx]
  ring

theorem nativePhysicalShellSource_smul_ae (a s c:ℝ) (U:NativeCollarL2) :
    nativePhysicalShellSource a s (c • U)=ᵐ[volume](c • nativePhysicalShellSource a s U) := by
  have h:=ae_comp_dilation (Real.exp_ne_zero (s-Real.log a))
    (ae_restrict_of_ae (s:=univ) (zeroShell_smul_ae c U))
  simp only [preimage_univ,Measure.restrict_univ] at h
  filter_upwards [h] with x hx
  simp only [nativePhysicalShellSource,Pi.smul_apply,smul_eq_mul] at hx ⊢
  rw [hx]
  ring

private def densityChartLinear (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M) (K:Set E) :
    (E→ℝ) →ₗ[ℝ] (M→ℝ) := by
  let L : (E→ℝ) →ₗ[ℝ] (E→ℝ) := {
    toFun := fun f x=>f x/gE.pullbackVolumeDensity id x
    map_add' := fun f h=>by ext x;simp only [Pi.add_apply,add_div]
    map_smul' := fun c f=>by
      simp only [RingHom.id_apply]
      ext x
      simp only [Pi.smul_apply,smul_eq_mul]
      ring }
  exact (nativeCompactChartFunctionLinear e K).comp L

private theorem densityChart_congr_ae
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:MeasurableSet K) {f h:E→ℝ} (hfh:f=ᵐ[volume]h) :
    nativeDensityCorrectedChartSource gE e K f=ᵐ[g.volumeMeasure]nativeDensityCorrectedChartSource gE e K h := by
  apply nativeCompactChart_congr_volume_ae g e he hei hK
  filter_upwards [ae_restrict_of_ae (s:=K) hfh] with x hx
  rw [hx]

private def shellNativeCriticalLinear
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (a s:ℝ)
    (hLp:∀U:NativeCollarL2,MemLp (nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a s U))
      (6/5:ℝ≥0∞) g.volumeMeasure) : NativeCollarL2 →ₗ[ℝ] Lp ℝ (6/5:ℝ≥0∞) g.volumeMeasure where
  toFun U:=(hLp U).toLp _
  map_add' U W:=by
    apply Lp.ext
    have ha:=densityChart_congr_ae g gE e he hei hK.measurableSet (nativePhysicalShellSource_add_ae a s U W)
    filter_upwards [(hLp (U+W)).coeFn_toLp,(hLp U).coeFn_toLp,(hLp W).coeFn_toLp,
      Lp.coeFn_add ((hLp U).toLp _) ((hLp W).toLp _),ha] with x hs hU hW hx hadd
    rw [hs,hx]
    simp only [Pi.add_apply]
    rw [hU,hW,hadd]
    simpa [densityChartLinear,nativeCompactChartFunctionLinear,nativeDensityCorrectedChartSource] using congrFun (map_add (densityChartLinear gE e K) (nativePhysicalShellSource a s U) (nativePhysicalShellSource a s W)) x
  map_smul' c U:=by
    simp only [RingHom.id_apply]
    apply Lp.ext
    have ha:=densityChart_congr_ae g gE e he hei hK.measurableSet (nativePhysicalShellSource_smul_ae a s c U)
    filter_upwards [(hLp (c • U)).coeFn_toLp,(hLp U).coeFn_toLp,
      Lp.coeFn_smul c ((hLp U).toLp _),ha] with x hs hU hx hsmul
    rw [hs,hx]
    simp only [Pi.smul_apply]
    rw [hU,hsmul]
    have hlin:=congrFun (map_smul (densityChartLinear gE e K) c (nativePhysicalShellSource a s U)) x
    dsimp [densityChartLinear,nativeCompactChartFunctionLinear] at hlin
    exact hlin

theorem exists_nativePhysicalShellSource_critical_CLM
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source) :
    ∃C:ℝ,0≤C ∧ ∀a:ℝ,0<a → ∀s:ℝ,
      ∃T:NativeCollarL2 →L[ℝ] Lp ℝ (6/5:ℝ≥0∞) g.volumeMeasure,
        ‖T‖≤C*Real.sqrt a*Real.exp (-2*s) ∧ ∀U:NativeCollarL2,
        MemLp (nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a s U)) 2 g.volumeMeasure ∧
        (T U:M→ℝ)=ᵐ[g.volumeMeasure]nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a s U) := by
  obtain ⟨D,hD,hd⟩:=exists_nativePhysicalShellSource_critical_bound g gE e he hei hK hKs
  refine ⟨D.toReal,ENNReal.toReal_nonneg,fun a ha s=>?_⟩
  have hm (U:NativeCollarL2):MemLp (nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a s U))
      (6/5:ℝ≥0∞) g.volumeMeasure := (hd a ha s U).2.1
  let L:=shellNativeCriticalLinear g gE e he hei hK a s hm
  have hb (U:NativeCollarL2):‖L U‖≤(D.toReal*Real.sqrt a*Real.exp (-2*s))*‖U‖ := by
    have ht:=ENNReal.toReal_mono (ENNReal.mul_ne_top hD ENNReal.ofReal_ne_top) (hd a ha s U).2.2
    have hn:ENNReal.ofReal ‖L U‖=eLpNorm (nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a s U))
        (6/5:ℝ≥0∞) g.volumeMeasure := by
      rw [ofReal_norm]
      exact Lp.enorm_toLp (hm U)
    rw [←hn,ENNReal.toReal_ofReal (norm_nonneg _),ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity:0≤Real.sqrt a*Real.exp (-2*s)*‖U‖)] at ht
    exact ht.trans_eq (by ring)
  let T:=L.mkContinuous (D.toReal*Real.sqrt a*Real.exp (-2*s)) hb
  exact ⟨T,LinearMap.mkContinuous_norm_le _ (by positivity) hb,fun U=>⟨(hd a ha s U).1,(hm U).coeFn_toLp⟩⟩

#print axioms nativePhysicalShellSource_add_ae
#print axioms nativePhysicalShellSource_smul_ae
#print axioms exists_nativePhysicalShellSource_critical_CLM
end Yamabe3.Analysis.SpherePolar
