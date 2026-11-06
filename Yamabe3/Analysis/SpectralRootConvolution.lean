import Yamabe3.Analysis.SpectralIntegralWeightedCauchy

/-!
# A genuine L2 square-root vector for the same spectral resolvent

Multiplying the scalar Green kernel by its own spectral rate removes the
1/k factor and yields -exp(-k|s|)/2. This defines a real operator-valued
L1 kernel. Its aggregate Bochner convolution supplies a genuine Hilbert
vector whose coordinates are k_i times the original solution coordinates.
There is no exchange of an unbounded spectral operator with an infinite
sum. The same fixed-point identity transfers the result to the accepted
integral-small potential inverse.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Filter MeasureTheory
open scoped Topology lp BoundedContinuousFunction Convolution

namespace Yamabe3.Analysis.Delaunay

def weightedSpectralRootKernel {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (δ t : ℝ) :
    SpectralSpace ι →L[ℝ] SpectralSpace ι :=
  Real.exp (-δ * t) • ((-(1 / 2 : ℝ)) • spectralPoissonKernel k hk₀ hk t)

theorem weightedSpectralRootKernel_norm_le {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (δ t : ℝ) :
    ‖weightedSpectralRootKernel k hk₀ hk δ t‖ ≤ k₀ * spectralMajorant k₀ δ t := by
  rw [weightedSpectralRootKernel, norm_smul, norm_smul,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  norm_num only [Real.norm_eq_abs, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ Real.exp (-δ * t) * ((1 / 2) * Real.exp (-k₀ * |t|)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (spectralPoissonKernel_norm_le k hk₀ hk t) (by norm_num))
        (Real.exp_pos _).le
    _ = _ := by
      unfold spectralMajorant
      rw [sub_eq_add_neg, Real.exp_add]
      field_simp [hk₀.ne']
      <;> ring

theorem weightedSpectralRootKernel_integrable {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀) :
    Integrable (weightedSpectralRootKernel k hk₀ hk δ) := by
  have hc : ContinuousOn (weightedSpectralRootKernel k hk₀ hk δ) ({0}ᶜ : Set ℝ) := by
    intro t ht
    have ht0 : t ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using ht
    have hP := spectralPoissonKernel_continuousAt k hk₀ hk ht0
    exact (((by fun_prop : ContinuousAt (fun s : ℝ => Real.exp (-δ * s)) t).smul
      (hP.const_smul (-(1 / 2 : ℝ))))).continuousWithinAt
  have hm : AEStronglyMeasurable (weightedSpectralRootKernel k hk₀ hk δ)
      (volume : Measure ℝ) := by
    simpa only [restrict_compl_singleton] using
      hc.aestronglyMeasurable (μ := volume) (measurableSet_singleton 0).compl
  exact ((spectralMajorant_integral hk₀ hδ).1.const_mul k₀).mono' hm
    (Eventually.of_forall (weightedSpectralRootKernel_norm_le k hk₀ hk δ))

def spectralRootConvolution {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (δ : ℝ)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) : SpectralSpace ι :=
  ∫ s : ℝ, weightedSpectralRootKernel k hk₀ hk δ s (F (t - s))

private theorem spectral_root_integrand_bound {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (δ : ℝ)
    (F : ℝ →ᵇ SpectralSpace ι) (t s : ℝ) :
    ‖weightedSpectralRootKernel k hk₀ hk δ s (F (t - s))‖ ≤
      (k₀ * spectralMajorant k₀ δ s) * ‖F‖ := by
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul (weightedSpectralRootKernel_norm_le k hk₀ hk δ s)
      (F.norm_coe_le_norm _) (norm_nonneg _)
      (mul_nonneg hk₀.le (spectralMajorant_nonneg hk₀ δ s)))

theorem spectralRootConvolution_integrable {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) :
    Integrable (fun s : ℝ => weightedSpectralRootKernel k hk₀ hk δ s (F (t - s))) := by
  apply (((spectralMajorant_integral hk₀ hδ).1.const_mul k₀).mul_const ‖F‖).mono'
  · exact ((ContinuousLinearMap.apply ℝ (SpectralSpace ι)).flip).aestronglyMeasurable_comp₂
      (weightedSpectralRootKernel_integrable k hk₀ hk hδ).aestronglyMeasurable
      (F.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall (spectral_root_integrand_bound k hk₀ hk δ F t)

theorem spectralRootConvolution_norm_le {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) :
    ‖spectralRootConvolution k hk₀ hk δ F t‖ ≤ k₀ * ‖F‖ / (k₀ ^ 2 - δ ^ 2) := by
  have h := norm_integral_le_of_norm_le
    (((spectralMajorant_integral hk₀ hδ).1.const_mul k₀).mul_const ‖F‖)
    (Eventually.of_forall (spectral_root_integrand_bound k hk₀ hk δ F t))
  rw [integral_mul_const, integral_const_mul, (spectralMajorant_integral hk₀ hδ).2] at h
  exact h.trans_eq (by ring)

theorem spectralRootConvolution_continuous {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F : ℝ →ᵇ SpectralSpace ι) :
    Continuous (spectralRootConvolution k hk₀ hk δ F) := by
  have hb : BddAbove (range (fun t : ℝ => ‖F t‖)) :=
    ⟨‖F‖, fun _ ⟨t, ht⟩ => ht ▸ F.norm_coe_le_norm t⟩
  exact hb.continuous_convolution_right_of_integrable
    (ContinuousLinearMap.apply ℝ (SpectralSpace ι)).flip
    (weightedSpectralRootKernel_integrable k hk₀ hk hδ) F.continuous

/-- Every coordinate belongs to one actual aggregate Hilbert vector. -/
theorem spectralRootConvolution_coordinate {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) (i : ι) :
    spectralRootConvolution k hk₀ hk δ F t i =
      k i * spectralResolvent k hk₀ hk hδ F t i := by
  let ev := lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i
  have hi := spectralRootConvolution_integrable k hk₀ hk hδ F t
  have hfree := spectralConvolution_integrable k hk₀ hk hδ F t
  have hev (s : ℝ) : ev (weightedSpectralRootKernel k hk₀ hk δ s (F (t - s))) =
      k i * ev (weightedSpectralKernel k hk₀ hk δ s (F (t - s))) := by
    change Real.exp (-δ * s) * (-(1 / 2) * (Real.exp (-k i * |s|) * F (t - s) i)) =
      k i * (Real.exp (-δ * s) * (scalarGreenKernel (k i) s * F (t - s) i))
    unfold scalarGreenKernel
    have hki : k i ≠ 0 := (hk₀.trans_le (hk i)).ne'
    field_simp [hki]
    <;> ring
  change ev (∫ s, weightedSpectralRootKernel k hk₀ hk δ s (F (t - s))) =
    k i * ev (∫ s, weightedSpectralKernel k hk₀ hk δ s (F (t - s)))
  rw [← ev.integral_comp_comm hi, ← ev.integral_comp_comm hfree]
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall hev)

/-- This is the same canonical fixed point's actual square-root vector. -/
def spectralIntegralPotentialRoot {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) : SpectralSpace ι :=
  let w := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F
  spectralRootConvolution k hk₀ hk δ (F - V • w) t

theorem spectralIntegralPotentialRoot_coordinate {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) (i : ι) :
    spectralIntegralPotentialRoot k hk₀ hk hδ hκ0 hκ1 V hV F t i =
      k i * spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F t i := by
  unfold spectralIntegralPotentialRoot
  rw [spectralRootConvolution_coordinate k hk₀ hk hδ]
  have he := spectralIntegralPotentialInverse_fixed k hk₀ hk hδ hκ0 hκ1 V hV F
  exact congrArg (fun w : ℝ →ᵇ SpectralSpace ι => k i * w t i) he

theorem spectralIntegralPotentialRoot_norm_le {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) :
    ‖spectralIntegralPotentialRoot k hk₀ hk hδ hκ0 hκ1 V hV F t‖ ≤
      (k₀ / (k₀ ^ 2 - δ ^ 2)) *
        (1 + ‖V‖ / ((k₀ ^ 2 - δ ^ 2) * (1 - κ))) * ‖F‖ := by
  let w := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F
  have hg := spectral_gap_positive hk₀ hδ
  have hw := spectralIntegralPotentialInverse_norm_le k hk₀ hk hδ hκ0 hκ1 V hV F
  have hsource : ‖F - V • w‖ ≤ ‖F‖ + ‖V‖ * ((‖F‖ / (k₀ ^ 2 - δ ^ 2)) / (1 - κ)) := by
    exact (norm_sub_le _ _).trans (add_le_add le_rfl
      ((norm_smul_le V w).trans (mul_le_mul_of_nonneg_left hw (norm_nonneg V))))
  unfold spectralIntegralPotentialRoot
  calc
    _ ≤ k₀ * ‖F - V • w‖ / (k₀ ^ 2 - δ ^ 2) :=
      spectralRootConvolution_norm_le k hk₀ hk hδ _ t
    _ ≤ k₀ * (‖F‖ + ‖V‖ * ((‖F‖ / (k₀ ^ 2 - δ ^ 2)) / (1 - κ))) /
        (k₀ ^ 2 - δ ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsource hk₀.le) hg.le
    _ = _ := by field_simp <;> ring

#print axioms spectralRootConvolution_coordinate
#print axioms spectralIntegralPotentialRoot_coordinate
#print axioms spectralIntegralPotentialRoot_norm_le

end Yamabe3.Analysis.Delaunay
