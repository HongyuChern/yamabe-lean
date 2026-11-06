import Yamabe3.Analysis.NativeScaledPhysicalSourceL2
import Yamabe3.Analysis.CriticalSourceDilation

/-! The ORIGINAL factor-eight source has critical norm O(sqrt(a)).
The zero extension, the source value and the inverse-square physical
amplitude are retained exactly. This is not a new forcing input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal BoundedContinuousFunction
namespace Yamabe3.Analysis
open UniformElliptic SpherePolar Delaunay
local notation "O" => (ball (0:E) 1\{(0:E)})

def originalSourceCriticalCost:ℝ :=
  (Real.sqrt 32*‖nativeSphereL2Inclusion‖)*((volume O)^(1/3:ℝ)).toReal

theorem zeroHalfEndPhysicalSource_critical_bound (f:HalfEndSourceValue) :
    MemLp (zeroHalfEndPhysicalSource f) (6/5:ℝ≥0∞) volume ∧
      eLpNorm (zeroHalfEndPhysicalSource f) (6/5:ℝ≥0∞) volume≤
        ENNReal.ofReal (originalSourceCriticalCost*‖f‖) := by
  have hO:MeasurableSet O := (isOpen_ball.sdiff isClosed_singleton).measurableSet
  have hvol:volume O<⊤ :=
    (measure_mono (sdiff_subset.trans ball_subset_closedBall)).trans_lt (isCompact_closedBall (0:E) 1).measure_lt_top
  letI:IsFiniteMeasure (volume.restrict O):=⟨by simpa only [Measure.restrict_apply_univ] using hvol⟩
  have hm:= (halfEndEuclideanPhysicalSource_memLp f).1
  have hp:MemLp (halfEndEuclideanPhysicalSource f) (6/5:ℝ≥0∞) (volume.restrict O) := hm.mono_exponent ((ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr (by norm_num))
  have hn:=eLpNorm_le_eLpNorm_mul_rpow_measure_univ ((ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr (by norm_num):(6/5:ℝ≥0∞)≤2) hm.1
  have he:eLpNorm (halfEndEuclideanPhysicalSource f) 2 (volume.restrict O)=
      ENNReal.ofReal ‖halfEndPhysicalSourceL2 f‖ := by
    rw [ofReal_norm]
    exact (Lp.enorm_toLp hm).symm
  have hv:((volume O)^(1/3:ℝ))≠⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hvol.ne
  refine ⟨(memLp_indicator_iff_restrict hO).mpr hp,?_⟩
  rw [zeroHalfEndPhysicalSource,eLpNorm_indicator_eq_eLpNorm_restrict hO]
  have hex:1/(6/5:ℝ≥0∞).toReal-1/(2:ℝ≥0∞).toReal=(1/3:ℝ) := by norm_num
  rw [hex,Measure.restrict_apply_univ,he] at hn
  apply hn.trans
  apply (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (halfEndPhysicalSourceL2_norm f)) zero_le).trans_eq
  have hcost:0≤originalSourceCriticalCost := by unfold originalSourceCriticalCost;positivity
  have hbase:0≤Real.sqrt 32*‖nativeSphereL2Inclusion‖ := by positivity
  have hid:ENNReal.ofReal originalSourceCriticalCost=
      ENNReal.ofReal (Real.sqrt 32*‖nativeSphereL2Inclusion‖)*(volume O)^(1/3:ℝ) := by
    unfold originalSourceCriticalCost
    exact (ENNReal.ofReal_mul hbase).trans (congrArg
      (fun q:ℝ≥0∞=>ENNReal.ofReal (Real.sqrt 32*‖nativeSphereL2Inclusion‖)*q) (ENNReal.ofReal_toReal hv))
  rw [ENNReal.ofReal_mul hcost,hid,ENNReal.ofReal_mul hbase]
  ring

def originalPhysicalSourceRescaling (a:ℝ) (f:HalfEndSourceValue) (x:E):ℝ :=
  (a^2)⁻¹*zeroHalfEndPhysicalSource f (a⁻¹ • x)

theorem originalPhysicalSourceRescaling_critical_bound
    {a:ℝ} (ha:0<a) (f:HalfEndSourceValue) :
    MemLp (originalPhysicalSourceRescaling a f) (6/5:ℝ≥0∞) volume ∧
      eLpNorm (originalPhysicalSourceRescaling a f) (6/5:ℝ≥0∞) volume≤
        ENNReal.ofReal (originalSourceCriticalCost*Real.sqrt a*‖f‖) := by
  have hF:=zeroHalfEndPhysicalSource_critical_bound f
  have hd:MemLp (fun x:E=>zeroHalfEndPhysicalSource f (a⁻¹ • x)) (6/5:ℝ≥0∞) volume := by
    simpa only [preimage_univ,Measure.restrict_univ] using
      memLp_comp_dilation (inv_ne_zero ha.ne') (hF.1.restrict univ)
  have he:Real.exp (-Real.log a)=a⁻¹ := by rw [Real.exp_neg,Real.exp_log ha]
  have hc:Real.exp (-2*Real.log a)=(a^2)⁻¹ := by
    calc
      _ = Real.exp (-(Real.log a+Real.log a)) := by congr 1;ring
      _ = (Real.exp (Real.log a)*Real.exp (Real.log a))⁻¹ := by rw [Real.exp_neg,Real.exp_add]
      _ = _ := by rw [Real.exp_log ha,pow_two]
  have hh:=eLpNorm_exp_cutoff_source_rescaling a ha 0 univ (zeroHalfEndPhysicalSource f)
  simp only [sub_zero,zero_sub,zero_div,add_zero,mul_zero,Real.exp_zero,mul_one,
    preimage_univ,Measure.restrict_univ,he,hc] at hh
  refine ⟨hd.const_mul _,?_⟩
  change eLpNorm (fun x:E=>(a^2)⁻¹*zeroHalfEndPhysicalSource f (a⁻¹ • x)) (6/5:ℝ≥0∞) volume≤_
  rw [hh]
  apply (mul_le_mul_of_nonneg_left hF.2 zero_le).trans_eq
  rw [←ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  congr 1
  ring

#print axioms zeroHalfEndPhysicalSource_critical_bound
#print axioms originalPhysicalSourceRescaling_critical_bound
end Yamabe3.Analysis
