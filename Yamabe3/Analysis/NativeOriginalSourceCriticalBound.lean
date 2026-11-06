import Yamabe3.Analysis.OriginalSourceCriticalDilation
import Yamabe3.Analysis.NativeChartCriticalTransport

/-! Uniform critical norm of the ORIGINAL density-corrected physical
source in the SAME native volume. The fixed compact density cost is
chosen before a and f; no a-dependent closed-graph cost is substituted. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology Manifold ENNReal
namespace Yamabe3.Analysis
open UniformElliptic SpherePolar Delaunay
local notation "O" => (ball (0:E) 1\{(0:E)})

private theorem inv_native_density_continuous (gE:RiemannianMetric 3 E) :
    Continuous (fun x:E=>(gE.pullbackVolumeDensity id x)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hh:=gE.contDiffAt_pullbackVolumeDensity (f:=id) (x:=x) contMDiffAt_id
    (by simpa using Function.injective_id)
  exact hh.1.continuousAt.inv₀ hh.2.ne'

theorem exists_originalScaledSource_fixed_compact_critical_bound
    (gE:RiemannianMetric 3 E) {K:Set E} (hK:IsCompact K) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀a:ℝ,0<a → ∀f:HalfEndSourceValue,
      MemLp (K.indicator (nativeScaledPhysicalSource gE a f)) (6/5:ℝ≥0∞) volume ∧
      eLpNorm (K.indicator (nativeScaledPhysicalSource gE a f)) (6/5:ℝ≥0∞) volume≤
        C*ENNReal.ofReal (Real.sqrt a*‖f‖) := by
  obtain ⟨D,hD⟩:=hK.exists_bound_of_continuousOn (inv_native_density_continuous gE).continuousOn
  let J:=max D 0
  have hJ:0≤J := le_max_right _ _
  refine ⟨ENNReal.ofReal (J*originalSourceCriticalCost),ENNReal.ofReal_ne_top,?_⟩
  intro a ha f
  have hf:=originalPhysicalSourceRescaling_critical_bound ha f
  have hi:MemLp (fun x:E=>(gE.pullbackVolumeDensity id x)⁻¹) ⊤ (volume.restrict K) :=
    continuousOn_compact_memLp_top hK (inv_native_density_continuous gE).continuousOn
  have hm:MemLp (nativeScaledPhysicalSource gE a f) (6/5:ℝ≥0∞) (volume.restrict K) := by
    apply ((hf.1.restrict K).mul' hi).ae_eq
    exact Eventually.of_forall fun x => by
      unfold nativeScaledPhysicalSource originalPhysicalSourceRescaling
      ring
  have hnorm:eLpNorm (nativeScaledPhysicalSource gE a f) (6/5:ℝ≥0∞) (volume.restrict K)≤
      ENNReal.ofReal J*eLpNorm (originalPhysicalSourceRescaling a f) (6/5:ℝ≥0∞) volume := by
    have hb:eLpNorm (nativeScaledPhysicalSource gE a f) (6/5:ℝ≥0∞) (volume.restrict K)≤
        eLpNorm (J • originalPhysicalSourceRescaling a f) (6/5:ℝ≥0∞) (volume.restrict K) := by
      apply eLpNorm_mono_ae
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      have hid:nativeScaledPhysicalSource gE a f x=
          originalPhysicalSourceRescaling a f x*(gE.pullbackVolumeDensity id x)⁻¹ := by
        unfold nativeScaledPhysicalSource originalPhysicalSourceRescaling
        ring
      rw [hid,norm_mul,Pi.smul_apply,norm_smul,Real.norm_of_nonneg hJ]
      exact (mul_le_mul_of_nonneg_left ((hD x hx).trans (le_max_left _ _)) (norm_nonneg _)).trans_eq (by ring)
    rw [eLpNorm_const_smul,Real.enorm_eq_ofReal hJ] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (eLpNorm_mono_measure _ Measure.restrict_le_self) zero_le)
  refine ⟨(memLp_indicator_iff_restrict hK.measurableSet).mpr hm,?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hK.measurableSet]
  apply (hnorm.trans (mul_le_mul_of_nonneg_left hf.2 zero_le)).trans_eq
  rw [←ENNReal.ofReal_mul hJ]
  have hcost:0≤originalSourceCriticalCost := by unfold originalSourceCriticalCost;positivity
  rw [←ENNReal.ofReal_mul (mul_nonneg hJ hcost)]
  congr 1
  ring

theorem nativeScaledPhysicalSource_zero_outside_closedBall
    (gE:RiemannianMetric 3 E) {a:ℝ} (ha:0<a) (f:HalfEndSourceValue)
    {x:E} (hx:x∉closedBall (0:E) a) : nativeScaledPhysicalSource gE a f x=0 := by
  have hy:a⁻¹ • x∉O := by
    intro hy
    have hn:‖a⁻¹ • x‖<1 := by simpa only [mem_ball_zero_iff] using hy.1
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le,←div_eq_inv_mul] at hn
    have hn':‖x‖<a := (div_lt_one ha).mp hn
    exact hx (by rw [mem_closedBall,dist_zero_right];exact hn'.le)
  simp only [nativeScaledPhysicalSource,zeroHalfEndPhysicalSource,indicator_of_notMem hy,zero_div]

variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem exists_nativeOriginalSource_critical_bound
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R:ℝ} (hsource:closedBall (0:E) R⊆e.source) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀a:ℝ,0<a → a≤R → ∀f:HalfEndSourceValue,
      MemLp (nativeCompactChartFunction e (closedBall (0:E) a) (nativeScaledPhysicalSource gE a f))
        (6/5:ℝ≥0∞) g.volumeMeasure ∧
      eLpNorm (nativeCompactChartFunction e (closedBall (0:E) a) (nativeScaledPhysicalSource gE a f))
        (6/5:ℝ≥0∞) g.volumeMeasure≤C*ENNReal.ofReal (Real.sqrt a*‖f‖) := by
  let K:=closedBall (0:E) R
  obtain ⟨D,hD,hd⟩:=exists_originalScaledSource_fixed_compact_critical_bound gE (isCompact_closedBall (0:E) R)
  obtain ⟨J,hJ,hj⟩:=exists_nativeCompactChart_critical_bound g e he hei (isCompact_closedBall (0:E) R) hsource
  refine ⟨J*D,ENNReal.mul_ne_top hJ hD,?_⟩
  intro a ha haR f
  have hf:=hd a ha f
  have hg:=hj (K.indicator (nativeScaledPhysicalSource gE a f)) hf.1
  have hi:K.indicator (K.indicator (nativeScaledPhysicalSource gE a f))=
      (closedBall (0:E) a).indicator (nativeScaledPhysicalSource gE a f) := by
    funext x
    by_cases hx:x∈closedBall (0:E) a
    · have hxK:x∈K := closedBall_subset_closedBall haR hx
      simp only [indicator_of_mem hx,indicator_of_mem hxK]
    · by_cases hxK:x∈K
      · simp only [indicator_of_notMem hx,indicator_of_mem hxK,
          nativeScaledPhysicalSource_zero_outside_closedBall gE ha f hx]
      · simp only [indicator_of_notMem hx,indicator_of_notMem hxK]
  have heq:nativeCompactChartFunction e K (K.indicator (nativeScaledPhysicalSource gE a f))=
      nativeCompactChartFunction e (closedBall (0:E) a) (nativeScaledPhysicalSource gE a f) := by
    unfold nativeCompactChartFunction
    rw [hi]
  rw [heq] at hg
  exact ⟨hg.1,hg.2.trans ((mul_le_mul_of_nonneg_left hf.2 zero_le).trans_eq (by ring))⟩

#print axioms exists_originalScaledSource_fixed_compact_critical_bound
#print axioms nativeScaledPhysicalSource_zero_outside_closedBall
#print axioms exists_nativeOriginalSource_critical_bound
end Yamabe3.Analysis
