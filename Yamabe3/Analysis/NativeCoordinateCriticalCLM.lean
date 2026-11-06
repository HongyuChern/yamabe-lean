import Yamabe3.Analysis.NativeCoordinatePullbackAe

/-! The native compact coordinate pullback is an actual bounded linear
operator on L6 classes. Its density cost is uniform before the input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
private instance criticalSix_ge_one:Fact (1 ≤ (6:ℝ≥0∞)) := ⟨by norm_num⟩
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

private def coordinateCriticalLinear
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (hm:∀f:Lp ℝ 6 g.volumeMeasure,MemLp (nativeCoordinateZeroPullback e K f) 6 volume) :
    Lp ℝ 6 g.volumeMeasure →ₗ[ℝ] Lp ℝ 6 (volume:Measure E) where
  toFun f:=(hm f).toLp _
  map_add' f h:=by
    apply Lp.ext
    have hlin:=nativeCoordinateZeroPullback_congr_six_ae g e he hei hK hKs
      (Lp.memLp (f+h)) ((Lp.memLp f).add (Lp.memLp h)) (Lp.coeFn_add f h)
    filter_upwards [(hm (f+h)).coeFn_toLp,(hm f).coeFn_toLp,(hm h).coeFn_toLp,
      Lp.coeFn_add ((hm f).toLp _) ((hm h).toLp _),hlin] with x hs hf hh hx hadd
    rw [hs,hx]
    simp only [Pi.add_apply]
    rw [hf,hh,hadd]
    exact congrFun (map_add (nativeCoordinateZeroPullbackLinear e K) (f:M→ℝ) (h:M→ℝ)) x
  map_smul' c f:=by
    simp only [RingHom.id_apply]
    apply Lp.ext
    have hlin:=nativeCoordinateZeroPullback_congr_six_ae g e he hei hK hKs
      (Lp.memLp (c • f)) ((Lp.memLp f).const_smul c) (Lp.coeFn_smul c f)
    filter_upwards [(hm (c • f)).coeFn_toLp,(hm f).coeFn_toLp,
      Lp.coeFn_smul c ((hm f).toLp _),hlin] with x hs hf hx hsmul
    rw [hs,hx]
    simp only [Pi.smul_apply]
    rw [hf,hsmul]
    exact congrFun (map_smul (nativeCoordinateZeroPullbackLinear e K) c (f:M→ℝ)) x

theorem exists_nativeCoordinate_critical_CLM
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source) :
    ∃C:ℝ,0 ≤ C ∧ ∃T:Lp ℝ 6 g.volumeMeasure →L[ℝ] Lp ℝ 6 (volume:Measure E),
      ‖T‖ ≤ C ∧ ∀f:Lp ℝ 6 g.volumeMeasure,
        (T f:E→ℝ)=ᵐ[volume]nativeCoordinateZeroPullback e K f := by
  obtain ⟨D,hD,hd⟩:=exists_nativeCoordinate_zero_pullback_six_bound g e he hei hK hKs
  have hm (f:Lp ℝ 6 g.volumeMeasure):MemLp (nativeCoordinateZeroPullback e K f) 6 volume := (hd f (Lp.memLp f)).1
  let L:=coordinateCriticalLinear g e he hei hK hKs hm
  have hb (f:Lp ℝ 6 g.volumeMeasure):‖L f‖ ≤ D.toReal*‖f‖ := by
    have ht:=ENNReal.toReal_mono (ENNReal.mul_ne_top hD (Lp.memLp f).2.ne) (hd f (Lp.memLp f)).2
    change ‖(hm f).toLp (nativeCoordinateZeroPullback e K f)‖ ≤ _
    rw [Lp.norm_toLp]
    simpa only [ENNReal.toReal_mul,Lp.norm_def] using ht
  let T:=L.mkContinuous D.toReal hb
  exact ⟨D.toReal,ENNReal.toReal_nonneg,T,LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg hb,fun f=>(hm f).coeFn_toLp⟩

#print axioms exists_nativeCoordinate_critical_CLM
end Yamabe3.Analysis.SpherePolar
