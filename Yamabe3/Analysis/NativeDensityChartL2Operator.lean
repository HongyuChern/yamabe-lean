import Yamabe3.Analysis.NativeDensityCorrectedChartLp
import Yamabe3.Analysis.NativeChartAeTransport
import Yamabe3.Analysis.WeakLaplacianDilation

/-! Actual bounded density-corrected native L2 transport for an
arbitrary Euclidean L2 source. This is a source-class producer, not a PDE
transport theorem. It retains the literal source and volume density. -/
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

private def densityNativeL2Linear
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K)
    (hLp:∀U:Lp ℝ 2 (volume:Measure E),MemLp (nativeDensityCorrectedChartSource gE e K (U:E→ℝ))
      2 g.volumeMeasure) : Lp ℝ 2 (volume:Measure E) →ₗ[ℝ] Lp ℝ 2 g.volumeMeasure where
  toFun U:=(hLp U).toLp _
  map_add' U W:=by
    apply Lp.ext
    have ha:=densityChart_congr_ae g gE e he hei hK.measurableSet (Lp.coeFn_add U W)
    filter_upwards [(hLp (U+W)).coeFn_toLp,(hLp U).coeFn_toLp,(hLp W).coeFn_toLp,
      Lp.coeFn_add ((hLp U).toLp _) ((hLp W).toLp _),ha] with x hs hU hW hx hadd
    rw [hs,hx]
    simp only [Pi.add_apply]
    rw [hU,hW,hadd]
    simpa [densityChartLinear,nativeCompactChartFunctionLinear,nativeDensityCorrectedChartSource] using congrFun (map_add (densityChartLinear gE e K) (U:E→ℝ) (W:E→ℝ)) x
  map_smul' c U:=by
    simp only [RingHom.id_apply]
    apply Lp.ext
    have ha:=densityChart_congr_ae g gE e he hei hK.measurableSet (Lp.coeFn_smul c U)
    filter_upwards [(hLp (c • U)).coeFn_toLp,(hLp U).coeFn_toLp,
      Lp.coeFn_smul c ((hLp U).toLp _),ha] with x hs hU hx hsmul
    rw [hs,hx]
    simp only [Pi.smul_apply]
    rw [hU,hsmul]
    have hlin:=congrFun (map_smul (densityChartLinear gE e K) c (U:E→ℝ)) x
    dsimp [densityChartLinear,nativeCompactChartFunctionLinear] at hlin
    exact hlin

theorem exists_nativeDensityCorrectedChartL2_CLM
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source) :
    ∃(C:ℝ) (T:Lp ℝ 2 (volume:Measure E) →L[ℝ] Lp ℝ 2 g.volumeMeasure),
      0 ≤ C ∧ ‖T‖ ≤ C ∧ ∀F:Lp ℝ 2 (volume:Measure E),
        (T F:M→ℝ)=ᵐ[g.volumeMeasure]nativeDensityCorrectedChartSource gE e K (F:E→ℝ) := by
  obtain ⟨D,hD,hd⟩:=exists_nativeDensityCorrectedChart_lp_bound g gE e he hei hK hKs 2
  have hm (F:Lp ℝ 2 (volume:Measure E)):MemLp (nativeDensityCorrectedChartSource gE e K (F:E→ℝ)) 2 g.volumeMeasure:=
    (hd (F:E→ℝ) (Lp.memLp F)).1
  let L:=densityNativeL2Linear g gE e he hei hK hm
  have hb (F:Lp ℝ 2 (volume:Measure E)):‖L F‖ ≤ D.toReal*‖F‖:=by
    have hi: eLpNorm (nativeDensityCorrectedChartSource gE e K (F:E→ℝ)) 2 g.volumeMeasure ≤ D*ENNReal.ofReal ‖F‖:=by
      simpa only [ofReal_norm,Lp.enorm_def] using (hd (F:E→ℝ) (Lp.memLp F)).2
    have ht:=ENNReal.toReal_mono (ENNReal.mul_ne_top hD ENNReal.ofReal_ne_top) hi
    have hn:ENNReal.ofReal ‖L F‖=eLpNorm (nativeDensityCorrectedChartSource gE e K (F:E→ℝ)) 2 g.volumeMeasure:=by
      rw [ofReal_norm]
      exact Lp.enorm_toLp (hm F)
    rw [←hn,ENNReal.toReal_ofReal (norm_nonneg _),ENNReal.toReal_mul,ENNReal.toReal_ofReal (norm_nonneg F)] at ht
    exact ht
  let T:=L.mkContinuous D.toReal hb
  exact ⟨D.toReal,T,ENNReal.toReal_nonneg,LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg hb,
    fun F=>(hm F).coeFn_toLp⟩

#print axioms exists_nativeDensityCorrectedChartL2_CLM
end Yamabe3.Analysis.SpherePolar
