import Yamabe3.Analysis.FutureL2Observables
import Yamabe3.Analysis.L2RealPairingBound

/-! Canonical continuous representatives of genuine L2 future tails.
The discontinuity of the kernel at zero is handled on its null slice. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

 theorem futureL2Kernel_memLp_two {k : ℝ} (hk : 0<k) : MemLp (futureL2Kernel k) 2 := by
  apply (memLp_two_iff_integrable_sq (futureL2Kernel_measurable k).aestronglyMeasurable).mpr
  have he : (fun t => futureL2Kernel k t^2)=futureL2Kernel (2*k) := by
    funext t
    by_cases ht : t∈Iic (0:ℝ)
    · simp only [futureL2Kernel,indicator_of_mem ht]
      rw [←Real.exp_nat_mul]
      congr 1
      ring
    · simp only [futureL2Kernel,indicator_of_notMem ht,zero_pow (by norm_num : 2≠0)]
  rw [he]
  exact (futureL2Kernel_mass (by positivity : 0<2*k)).1

 theorem futureL2Kernel_translate_memLp {k : ℝ} (hk : 0<k) (t : ℝ) :
    MemLp (fun s => futureL2Kernel k (t-s)) 2 :=
  (futureL2Kernel_memLp_two hk).comp_measurePreserving (volume.measurePreserving_sub_left t)

 theorem futureL2Kernel_continuousAt (k : ℝ) {x : ℝ} (hx : x≠0) :
    ContinuousAt (futureL2Kernel k) x := by
  by_cases hn : x<0
  · have he : futureL2Kernel k=ᶠ[𝓝 x](fun t => Real.exp (k*t)) := by
      filter_upwards [Iio_mem_nhds hn] with t ht
      exact indicator_of_mem (show t∈Iic (0:ℝ) from (show t < 0 from ht).le) _
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt).congr_of_eventuallyEq he
  · have hp : 0<x := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hx)
    have he : futureL2Kernel k=ᶠ[𝓝 x](fun _ => (0:ℝ)) := by
      filter_upwards [Ioi_mem_nhds hp] with t ht
      exact indicator_of_notMem (show t∉Iic (0:ℝ) from not_le.mpr (show 0 < t from ht)) _
    exact continuousAt_const.congr_of_eventuallyEq he

 theorem futureL2Kernel_local_domination {k : ℝ} (hk : 0<k) {t t₀ : ℝ}
    (ht : |t-t₀|≤1) (s : ℝ) :
    futureL2Kernel k (t-s)≤Real.exp (2*k)*futureL2Kernel k ((t₀-1)-s) := by
  by_cases hs : t ≤ s
  · have hb : (t₀-1)-s∈Iic (0:ℝ) := by
      have h := (abs_le.mp ht).1
      change (t₀-1)-s ≤ 0
      linarith
    rw [futureL2Kernel,indicator_of_mem (show t-s∈Iic (0:ℝ) from sub_nonpos.mpr hs),indicator_of_mem hb,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := (abs_le.mp ht).2
    nlinarith
  · rw [futureL2Kernel,indicator_of_notMem (show t-s∉Iic (0:ℝ) from by simpa only [mem_Iic,sub_nonpos] using hs)]
    exact mul_nonneg (Real.exp_pos _).le (futureL2Kernel_nonneg k ((t₀-1)-s))

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

 theorem futureL2Convolution_everywhere_integrable {k : ℝ} (hk : 0<k)
    (F : ℝ → H) (hF : MemLp F 2) (t : ℝ) :
    Integrable (fun s : ℝ => futureL2Kernel k (t-s) • F s) := by
  have hi := (futureL2Kernel_translate_memLp hk t).integrable_mul hF.norm
  apply hi.mono'
  · exact (((futureL2Kernel_measurable k).comp (measurable_const.sub measurable_id)).aestronglyMeasurable).smul hF.1
  · exact Eventually.of_forall fun s => by
      rw [norm_smul,Real.norm_of_nonneg (futureL2Kernel_nonneg k (t-s))]
      exact le_rfl

 theorem futureL2Convolution_continuous {k : ℝ} (hk : 0<k)
    (F : ℝ → H) (hF : MemLp F 2) : Continuous (futureL2Convolution k F) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  have hi := ((futureL2Kernel_translate_memLp hk (t₀-1)).integrable_mul hF.norm).const_mul (Real.exp (2*k))
  apply continuousAt_of_dominated (bound := fun s => Real.exp (2*k)*(futureL2Kernel k ((t₀-1)-s)*‖F s‖))
  · exact Eventually.of_forall fun t => (futureL2Convolution_everywhere_integrable hk F hF t).1
  · filter_upwards [Metric.ball_mem_nhds t₀ (by norm_num : (0:ℝ)<1)] with t ht
    have ht1 : |t-t₀|≤1 := by simpa only [Metric.mem_ball,Real.dist_eq] using ht.le
    exact Eventually.of_forall fun s => by
      rw [norm_smul,Real.norm_of_nonneg (futureL2Kernel_nonneg k (t-s)),←mul_assoc]
      exact mul_le_mul_of_nonneg_right (futureL2Kernel_local_domination hk ht1 s) (norm_nonneg _)
  · exact hi
  · have hn : ∀ᵐ s : ℝ ∂volume,s≠t₀ := by
      apply ae_iff.mpr
      simp
    filter_upwards [hn] with s hs
    have hsub : ContinuousAt (fun t : ℝ => t-s) t₀ :=
      (continuous_id.sub continuous_const).continuousAt
    have hk' : ContinuousAt (futureL2Kernel k) (t₀-s) :=
      futureL2Kernel_continuousAt k (sub_ne_zero.mpr (Ne.symm hs))
    exact (ContinuousAt.comp (f := fun t : ℝ => t-s) (x := t₀) hk' hsub).smul continuousAt_const

 theorem futureL2Convolution_uniform_norm {k : ℝ} (hk : 0<k)
    (F : Lp H 2 (volume : Measure ℝ)) (t : ℝ) :
    ‖futureL2Convolution k F t‖≤(eLpNorm (futureL2Kernel k) 2).toReal*‖F‖ := by
  have hK := futureL2Kernel_translate_memLp hk t
  have hi := hK.integrable_mul (Lp.memLp F).norm
  have hb : ‖futureL2Convolution k F t‖≤∫ s : ℝ,futureL2Kernel k (t-s)*‖F s‖ := by
    apply norm_integral_le_of_norm_le hi
    exact Eventually.of_forall fun s => by
      rw [norm_smul,Real.norm_of_nonneg (futureL2Kernel_nonneg k (t-s))]
      exact le_rfl
  apply hb.trans
  have hn := integral_mul_le_eLpNorm_two volume hK (Lp.memLp F).norm
  have he := eLpNorm_comp_measurePreserving (p := (2:ℝ≥0∞))
    (futureL2Kernel_memLp_two hk).1 (volume.measurePreserving_sub_left t)
  change eLpNorm (fun s => futureL2Kernel k (t-s)) 2=eLpNorm (futureL2Kernel k) 2 at he
  simpa only [he,eLpNorm_norm,Lp.norm_def] using hn

#print axioms futureL2Kernel_memLp_two
#print axioms futureL2Kernel_local_domination
#print axioms futureL2Convolution_everywhere_integrable
#print axioms futureL2Convolution_continuous
#print axioms futureL2Convolution_uniform_norm
end Yamabe3.Analysis.Delaunay
