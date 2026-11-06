import Yamabe3.Analysis.SpectralL2EntranceRegularity
import Yamabe3.Analysis.SpectralFirstDerivativeConvolution

/-! The actual derivative of the weighted Green integral gains a half
spectral order at the entrance. This is a proved source estimate, not a
fractional trace assumption. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem weightedSpectralFirstDerivativeKernel_coordinate_norm {ι : Type*}
    (k : ι → ℝ) {k₀ : ℝ} (hk₀ : 0<k₀) (hk : ∀ i,k₀≤k i)
    (δ t : ℝ) (u : SpectralSpace ι) (i : ι) :
    ‖weightedSpectralFirstDerivativeKernel k hk₀ hk δ t u i‖=
      k i*spectralMajorant (k i) δ t*‖u i‖ := by
  rw [weightedSpectralFirstDerivativeKernel_apply]
  have hc : ‖if 0≤t then (1/2:ℝ) else -(1/2:ℝ)‖=1/2 := by split_ifs <;> norm_num
  rw [norm_mul,norm_mul,norm_mul,hc,Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  unfold spectralMajorant
  rw [sub_eq_add_neg,Real.exp_add]
  have hki := (hk₀.trans_le (hk i)).ne'
  field_simp
  <;> ring

theorem spectralFirstDerivativeConvolution_coordinate_square_bound {ι : Type*}
    (k : ι → ℝ) {k₀ δ : ℝ} (hk₀ : 0<k₀) (hk : ∀ i,k₀≤k i) (hδ : |δ|<k₀)
    (F : ℝ →ᵇ SpectralSpace ι) (hF : MemLp F 2) (t : ℝ) (i : ι) :
    (spectralFirstDerivativeConvolution k hk₀ hk δ F t i)^2≤
      (k i)^2*(1/(4*k i*(k i^2-δ^2)))*(∫ s : ℝ,(F s i)^2) := by
  let ev := lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i
  have he : spectralFirstDerivativeConvolution k hk₀ hk δ F t i=
      ∫ s : ℝ,weightedSpectralFirstDerivativeKernel k hk₀ hk δ s (F (t-s)) i := by
    exact (ev.integral_comp_comm (spectralFirstDerivativeConvolution_integrable k hk₀ hk hδ F t)).symm
  have hn : |spectralFirstDerivativeConvolution k hk₀ hk δ F t i|≤
      k i*(∫ s : ℝ,spectralMajorant (k i) δ (t-s)*|F s i|) := by
    rw [he]
    have h := norm_integral_le_integral_norm (μ := volume) (fun s : ℝ =>
      weightedSpectralFirstDerivativeKernel k hk₀ hk δ s (F (t-s)) i)
    simp_rw [weightedSpectralFirstDerivativeKernel_coordinate_norm] at h
    rw [show (fun s : ℝ => k i*spectralMajorant (k i) δ s*‖F (t-s) i‖)=
      fun s => k i*(spectralMajorant (k i) δ s*‖F (t-s) i‖) by funext s;ring,
      integral_const_mul] at h
    rw [←integral_sub_left_eq_self (fun s : ℝ => spectralMajorant (k i) δ s*‖F (t-s) i‖) volume t] at h
    simpa only [sub_sub_cancel,Real.norm_eq_abs] using h
  have hki := hk₀.trans_le (hk i)
  have hδi := hδ.trans_le (hk i)
  have hFi := (lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i).comp_memLp' hF
  have hc := integral_mul_sq_le_integral_sq_mul volume
    (spectralMajorant_translate_memLp hki hδi t) hFi.norm
  have heI : (∫ s : ℝ,spectralMajorant (k i) δ (t-s)^2)=1/(4*k i*(k i^2-δ^2)) := by
    rw [integral_sub_left_eq_self (fun s : ℝ => spectralMajorant (k i) δ s^2) volume t]
    exact spectralMajorant_square_integral hki hδi
  simp only [Real.norm_eq_abs,sq_abs] at hc
  rw [heI] at hc
  change (∫ s : ℝ,spectralMajorant (k i) δ (t-s)*|F s i|)^2≤
    (1/(4*k i*(k i^2-δ^2)))*(∫ s : ℝ,(F s i)^2) at hc
  have hnn : 0≤k i*(∫ s : ℝ,spectralMajorant (k i) δ (t-s)*|F s i|) :=
    mul_nonneg hki.le (integral_nonneg fun s => mul_nonneg (spectralMajorant_nonneg hki δ (t-s)) (abs_nonneg _))
  have hs := (sq_le_sq₀ (abs_nonneg _) hnn).mpr hn
  rw [sq_abs,mul_pow] at hs
  exact hs.trans ((mul_le_mul_of_nonneg_left hc (sq_nonneg _)).trans_eq (by ring))

theorem spectralFirstDerivativeConvolution_finite_entrance_budget {ι : Type*}
    (k : ι → ℝ) {k₀ δ : ℝ} (hk₀ : 0<k₀) (hk : ∀ i,k₀≤k i) (hδ : |δ|<k₀)
    (F : ℝ →ᵇ SpectralSpace ι) (hF : MemLp F 2) (t : ℝ) (s : Finset ι) :
    (∑ i ∈ s,k i*(spectralFirstDerivativeConvolution k hk₀ hk δ F t i)^2)≤
      (k₀^2/(4*(k₀^2-δ^2)))*(∫ a : ℝ,‖F a‖^2) := by
  have hpoint (i : ι) : k i*(spectralFirstDerivativeConvolution k hk₀ hk δ F t i)^2≤
      (k₀^2/(4*(k₀^2-δ^2)))*(∫ a : ℝ,(F a i)^2) := by
    have h := mul_le_mul_of_nonneg_left
      (spectralFirstDerivativeConvolution_coordinate_square_bound k hk₀ hk hδ F hF t i)
      (hk₀.trans_le (hk i)).le
    have hr := mul_le_mul_of_nonneg_right (spectral_rate_cubic_kernel_bound hk₀ (hk i) hδ)
      (integral_nonneg (μ := volume) fun a : ℝ => sq_nonneg (F a i))
    nlinarith only [h,hr]
  have hs := Finset.sum_le_sum (fun i (_ : i∈s) => hpoint i)
  rw [←Finset.mul_sum] at hs
  have hg := spectral_gap_positive hk₀ hδ
  exact hs.trans (mul_le_mul_of_nonneg_left (spectralL2_finite_coordinate_integral_bound F hF s) (by positivity))

theorem spectralFirstDerivativeConvolution_entrance_spectral_regular {ι : Type*}
    (k : ι → ℝ) {k₀ δ : ℝ} (hk₀ : 0<k₀) (hk : ∀ i,k₀≤k i) (hδ : |δ|<k₀)
    (F : ℝ →ᵇ SpectralSpace ι) (hF : MemLp F 2) (t : ℝ) :
    Summable (fun i => k i*(spectralFirstDerivativeConvolution k hk₀ hk δ F t i)^2) ∧
      (∑' i,k i*(spectralFirstDerivativeConvolution k hk₀ hk δ F t i)^2)≤
        (k₀^2/(4*(k₀^2-δ^2)))*(∫ a : ℝ,‖F a‖^2) := by
  have hn : 0≤(fun i => k i*(spectralFirstDerivativeConvolution k hk₀ hk δ F t i)^2) :=
    fun i => mul_nonneg (hk₀.trans_le (hk i)).le (sq_nonneg _)
  have hb := spectralFirstDerivativeConvolution_finite_entrance_budget k hk₀ hk hδ F hF t
  exact ⟨summable_of_sum_le hn hb,Real.tsum_le_of_sum_le hn hb⟩

#print axioms weightedSpectralFirstDerivativeKernel_coordinate_norm
#print axioms spectralFirstDerivativeConvolution_coordinate_square_bound
#print axioms spectralFirstDerivativeConvolution_finite_entrance_budget
#print axioms spectralFirstDerivativeConvolution_entrance_spectral_regular
end Yamabe3.Analysis.Delaunay
