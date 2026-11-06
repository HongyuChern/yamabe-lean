import Yamabe3.Analysis.SpectralL2CoordinateEntrance

/-! Uniform finite and infinite spectral entrance budgets for the
actual L2 free convolution. The rate cubed is the square of the true
three-halves boundary weight, with its sharp scalar denominator retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ENNReal lp
namespace Yamabe3.Analysis.Delaunay

theorem spectral_rate_cubic_kernel_bound {k₀ k δ : ℝ}
    (hk₀ : 0<k₀) (hk : k₀ ≤ k) (hδ : |δ|<k₀) :
    k^3*(1/(4*k*(k^2-δ^2))) ≤ k₀^2/(4*(k₀^2-δ^2)) := by
  have hk0 := hk₀.trans_le hk
  have hg := spectral_gap_positive hk0 (hδ.trans_le hk)
  have hg0 := spectral_gap_positive hk₀ hδ
  have he : k^3*(1/(4*k*(k^2-δ^2)))=k^2/(4*(k^2-δ^2)) := by
    field_simp
  rw [he]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hsq : k₀^2 ≤ k^2 := pow_le_pow_left₀ hk₀.le hk 2
  nlinarith [mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hsq)]

theorem spectralL2_finite_coordinate_integral_bound {ι : Type*}
    (F : ℝ → SpectralSpace ι) (hF : MemLp F 2) (s : Finset ι) :
    (∑ i ∈ s,∫ t : ℝ,(F t i)^2) ≤ ∫ t : ℝ,‖F t‖^2 := by
  have hFi (i : ι) : MemLp (fun t => F t i) 2 :=
    (lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i).comp_memLp' hF
  rw [←integral_finsetSum s (fun i _ => (hFi i).integrable_sq)]
  apply integral_mono (integrable_finsetSum s (fun i _ => (hFi i).integrable_sq))
    ((memLp_two_iff_integrable_sq_norm hF.1).mp hF)
  intro t
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using
    lp.sum_rpow_le_norm_rpow (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal) (F t) s

theorem spectralL2Convolution_finite_entrance_budget {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F : ℝ → SpectralSpace ι) (hF : MemLp F 2) (t : ℝ) (s : Finset ι) :
    (∑ i ∈ s,k i^3*(spectralL2Convolution k hk₀ hk δ F t i)^2) ≤
      (k₀^2/(4*(k₀^2-δ^2)))*(∫ a : ℝ,‖F a‖^2) := by
  have hpoint (i : ι) : k i^3*(spectralL2Convolution k hk₀ hk δ F t i)^2 ≤
      (k₀^2/(4*(k₀^2-δ^2)))*(∫ a : ℝ,(F a i)^2) := by
    have h := mul_le_mul_of_nonneg_left
      (spectralL2Convolution_coordinate_square_bound k hk₀ hk hδ F hF t i)
      (pow_nonneg (hk₀.trans_le (hk i)).le 3)
    rw [←mul_assoc] at h
    exact h.trans (mul_le_mul_of_nonneg_right (spectral_rate_cubic_kernel_bound hk₀ (hk i) hδ)
      (integral_nonneg fun _ => sq_nonneg _))
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ s) => hpoint i)
  rw [←Finset.mul_sum] at hs
  have hg := spectral_gap_positive hk₀ hδ
  exact hs.trans (mul_le_mul_of_nonneg_left (spectralL2_finite_coordinate_integral_bound F hF s) (by positivity))

theorem spectralL2Convolution_entrance_spectral_regular {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F : ℝ → SpectralSpace ι) (hF : MemLp F 2) (t : ℝ) :
    Summable (fun i => k i^3*(spectralL2Convolution k hk₀ hk δ F t i)^2) ∧
      (∑' i,k i^3*(spectralL2Convolution k hk₀ hk δ F t i)^2) ≤
        (k₀^2/(4*(k₀^2-δ^2)))*(∫ a : ℝ,‖F a‖^2) := by
  have hn : 0 ≤ (fun i => k i^3*(spectralL2Convolution k hk₀ hk δ F t i)^2) :=
    fun i => mul_nonneg (pow_nonneg (hk₀.trans_le (hk i)).le 3) (sq_nonneg _)
  have hb := spectralL2Convolution_finite_entrance_budget k hk₀ hk hδ F hF t
  exact ⟨summable_of_sum_le hn hb,Real.tsum_le_of_sum_le hn hb⟩

#print axioms spectral_rate_cubic_kernel_bound
#print axioms spectralL2_finite_coordinate_integral_bound
#print axioms spectralL2Convolution_finite_entrance_budget
#print axioms spectralL2Convolution_entrance_spectral_regular
end Yamabe3.Analysis.Delaunay
