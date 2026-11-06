import Yamabe3.Analysis.SpectralFirstDerivativeKernel
import Yamabe3.Analysis.SpectralCoordinateEquation
import Yamabe3.Analysis.SpectralCoordinateFTC
import Yamabe3.Analysis.TwoRateWeightedDerivative

/-!
# The genuine strong derivative of the same spectral resolvent

The derivative candidate is an actual Bochner convolution with a bounded
diagonal kernel.  Its continuity and aggregate norm bound are proved before
taking any coordinate.  Coordinate evaluation identifies its scalar tails;
the Hilbert fundamental theorem then proves the strong derivative of the
original weighted resolvent.  Unbounded spectral rates cause no exchange
of an infinite sum with a time supremum.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Filter MeasureTheory
open scoped Topology lp BoundedContinuousFunction Convolution

namespace Yamabe3.Analysis.Delaunay

def spectralFirstDerivativeConvolution {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (δ : ℝ)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) : SpectralSpace ι :=
  ∫ s : ℝ, weightedSpectralFirstDerivativeKernel k hk₀ hk δ s (F (t - s))

private theorem spectral_first_derivative_integrand_bound {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (δ : ℝ)
    (F : ℝ →ᵇ SpectralSpace ι) (t s : ℝ) :
    ‖weightedSpectralFirstDerivativeKernel k hk₀ hk δ s (F (t - s))‖ ≤
      (k₀ * spectralMajorant k₀ δ s) * ‖F‖ := by
  calc
    _ ≤ ‖weightedSpectralFirstDerivativeKernel k hk₀ hk δ s‖ * ‖F (t - s)‖ :=
      (weightedSpectralFirstDerivativeKernel k hk₀ hk δ s).le_opNorm _
    _ ≤ (k₀ * spectralMajorant k₀ δ s) * ‖F‖ :=
      mul_le_mul (weightedSpectralFirstDerivativeKernel_norm_le k hk₀ hk δ s)
        (F.norm_coe_le_norm _) (norm_nonneg _)
        (mul_nonneg hk₀.le (spectralMajorant_nonneg hk₀ δ s))

theorem spectralFirstDerivativeConvolution_integrable {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) :
    Integrable (fun s : ℝ => weightedSpectralFirstDerivativeKernel k hk₀ hk δ s (F (t - s))) := by
  apply (((spectralMajorant_integral hk₀ hδ).1.const_mul k₀).mul_const ‖F‖).mono'
  · exact ((ContinuousLinearMap.apply ℝ (SpectralSpace ι)).flip).aestronglyMeasurable_comp₂
      (weightedSpectralFirstDerivativeKernel_integrable k hk₀ hk hδ).aestronglyMeasurable
      (F.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall (spectral_first_derivative_integrand_bound k hk₀ hk δ F t)

theorem spectralFirstDerivativeConvolution_norm_le {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) :
    ‖spectralFirstDerivativeConvolution k hk₀ hk δ F t‖ ≤
      k₀ * ‖F‖ / (k₀ ^ 2 - δ ^ 2) := by
  have h := norm_integral_le_of_norm_le
    (((spectralMajorant_integral hk₀ hδ).1.const_mul k₀).mul_const ‖F‖)
    (Eventually.of_forall (spectral_first_derivative_integrand_bound k hk₀ hk δ F t))
  rw [integral_mul_const, integral_const_mul, (spectralMajorant_integral hk₀ hδ).2] at h
  exact h.trans_eq (by ring)

theorem spectralFirstDerivativeConvolution_continuous {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F : ℝ →ᵇ SpectralSpace ι) :
    Continuous (spectralFirstDerivativeConvolution k hk₀ hk δ F) := by
  have hb : BddAbove (range (fun t : ℝ => ‖F t‖)) :=
    ⟨‖F‖, fun _ ⟨t, ht⟩ => ht ▸ F.norm_coe_le_norm t⟩
  exact hb.continuous_convolution_right_of_integrable
    (ContinuousLinearMap.apply ℝ (SpectralSpace ι)).flip
    (weightedSpectralFirstDerivativeKernel_integrable k hk₀ hk hδ) F.continuous

/-- Coordinate evaluation of this actual Hilbert convolution is exactly
the difference of the two scalar exponential tails. -/
theorem spectralFirstDerivativeConvolution_coordinate {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) (i : ι) :
    spectralFirstDerivativeConvolution k hk₀ hk δ F t i =
      (Real.exp (-(k i + δ) * t) * leftTail (fun y => Real.exp ((k i + δ) * y) * F y i) t -
        Real.exp ((k i - δ) * t) * rightTail (fun y => Real.exp (-(k i - δ) * y) * F y i) t) / 2 := by
  let ev := lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i
  have hi := spectralFirstDerivativeConvolution_integrable k hk₀ hk hδ F t
  let H : ℝ → ℝ := fun s => Real.exp (-δ * s) *
    (if 0 ≤ s then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) * Real.exp (-k i * |s|) * F (t - s) i
  have hev (s : ℝ) : ev (weightedSpectralFirstDerivativeKernel k hk₀ hk δ s (F (t - s))) = H s :=
    weightedSpectralFirstDerivativeKernel_apply k hk₀ hk δ s (F (t - s)) i
  have hc : spectralFirstDerivativeConvolution k hk₀ hk δ F t i = ∫ s : ℝ, H s := by
    change ev (∫ s : ℝ, weightedSpectralFirstDerivativeKernel k hk₀ hk δ s (F (t - s))) = _
    rw [← ev.integral_comp_comm hi]
    exact integral_congr_ae (Eventually.of_forall hev)
  have hci : Integrable H := (ev.integrable_comp hi).congr (Eventually.of_forall hev)
  let Q : ℝ → ℝ := fun y => H (t - y)
  have hQ : Integrable Q := hci.comp_sub_left t
  have hchange : spectralFirstDerivativeConvolution k hk₀ hk δ F t i = ∫ y : ℝ, Q y := by
    rw [hc, ← integral_sub_left_eq_self H volume t]
  have hL (y : ℝ) (hy : y ∈ Iic t) :
      Q y = (Real.exp (-(k i + δ) * t) / 2) *
        (Real.exp ((k i + δ) * y) * F y i) := by
    dsimp only [Q, H]
    rw [sub_sub_cancel, if_pos (sub_nonneg.mpr hy), abs_of_nonneg (sub_nonneg.mpr hy)]
    have he : Real.exp (-δ * (t - y)) * Real.exp (-k i * (t - y)) =
        Real.exp (-(k i + δ) * t) * Real.exp ((k i + δ) * y) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = (Real.exp (-δ * (t - y)) * Real.exp (-k i * (t - y))) * F y i / 2 := by ring
      _ = _ := by rw [he]; ring
  have hR (y : ℝ) (hy : y ∈ Ioi t) :
      Q y = -(Real.exp ((k i - δ) * t) / 2) *
        (Real.exp (-(k i - δ) * y) * F y i) := by
    dsimp only [Q, H]
    rw [sub_sub_cancel, if_neg (not_le.mpr (sub_neg.mpr hy)),
      abs_of_nonpos (sub_nonpos.mpr hy.le)]
    have he : Real.exp (-δ * (t - y)) * Real.exp (-k i * -(t - y)) =
        Real.exp ((k i - δ) * t) * Real.exp (-(k i - δ) * y) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = -(Real.exp (-δ * (t - y)) * Real.exp (-k i * -(t - y))) * F y i / 2 := by ring
      _ = _ := by rw [he]; ring
  rw [hchange, ← integral_add_compl measurableSet_Iic hQ, compl_Iic]
  rw [setIntegral_congr_fun measurableSet_Iic hL, setIntegral_congr_fun measurableSet_Ioi hR,
    integral_const_mul, integral_const_mul]
  unfold leftTail rightTail
  ring

/-- The original weighted spectral resolvent has this actual strong
Hilbert derivative; the candidate is not merely a list of coordinate bounds. -/
theorem spectralResolvent_weighted_hasDerivAt {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) :
    HasDerivAt (fun s => Real.exp (δ * s) • spectralResolvent k hk₀ hk hδ F s)
      (Real.exp (δ * t) • spectralFirstDerivativeConvolution k hk₀ hk δ F t) t := by
  have hV : Continuous (fun s => Real.exp (δ * s) • spectralFirstDerivativeConvolution k hk₀ hk δ F s) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      (spectralFirstDerivativeConvolution_continuous k hk₀ hk hδ F)
  apply hasDerivAt_spectral_of_continuous_coordinate_derivative hV
  intro s i
  have heq : (fun y => (Real.exp (δ * y) • spectralResolvent k hk₀ hk hδ F y) i) =
      (fun y => Real.exp (δ * y) * twoRateInverse (k i + δ) (k i - δ) (fun x => F x i) y) := by
    funext y
    change Real.exp (δ * y) * spectralConvolution k hk₀ hk δ F y i = _
    rw [spectralConvolution_coordinate k hk₀ hk hδ]
  rw [heq]
  change HasDerivAt _ (Real.exp (δ * s) * spectralFirstDerivativeConvolution k hk₀ hk δ F s i) s
  rw [spectralFirstDerivativeConvolution_coordinate k hk₀ hk hδ]
  exact weighted_twoRateInverse_hasDerivAt (hk₀.trans_le (hk i)) (hδ.trans_le (hk i))
    (spectralCoordinate_continuous F i) (fun y => spectralCoordinate_bound F y i) s

theorem spectralResolvent_weighted_derivative_bound {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) :
    ‖deriv (fun s => Real.exp (δ * s) • spectralResolvent k hk₀ hk hδ F s) t‖ ≤
      (k₀ * ‖F‖ / (k₀ ^ 2 - δ ^ 2)) * Real.exp (δ * t) := by
  rw [(spectralResolvent_weighted_hasDerivAt k hk₀ hk hδ F t).deriv,
    norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact (mul_le_mul_of_nonneg_left
    (spectralFirstDerivativeConvolution_norm_le k hk₀ hk hδ F t) (Real.exp_pos _).le).trans_eq
      (by ring)

#print axioms spectralFirstDerivativeConvolution_continuous
#print axioms spectralResolvent_weighted_hasDerivAt
#print axioms spectralResolvent_weighted_derivative_bound

end Yamabe3.Analysis.Delaunay
