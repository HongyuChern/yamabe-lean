import Yamabe3.Analysis.SpectralKernelIntegral
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The actual first derivative kernel on the spectral Hilbert space

The exponential diagonal has a bounded operator norm even for unbounded
spectral rates.  It is norm-continuous away from time zero; continuity at
zero is not asserted.  The signed derivative kernel is therefore strongly
measurable almost everywhere and genuinely Bochner integrable.  Its exact
two-rate majorant has integral k0/(k0^2-delta^2).
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open Set Filter MeasureTheory
open scoped Topology lp

namespace Yamabe3.Analysis.Delaunay

private theorem scalar_exponential_rate_bound {k ε x : ℝ}
    (hk : 0 < k) (hε : 0 < ε) (hx : ε ≤ x) :
    k * Real.exp (-k * x) ≤ ε⁻¹ := by
  have hxpos : 0 < x := hε.trans_le hx
  have hnum : (k * x) * Real.exp (-(k * x)) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one (k * x)).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  rw [← neg_mul] at hnum
  calc
    k * Real.exp (-k * x) ≤ 1 / x := by
      apply (le_div_iff₀ hxpos).mpr
      nlinarith only [hnum]
    _ ≤ 1 / ε := one_div_le_one_div_of_le hε hx
    _ = ε⁻¹ := one_div _

private theorem scalar_exponential_lipschitz_away_zero {k ε s t : ℝ}
    (hk : 0 < k) (hε : 0 < ε) (hs : ε ≤ s) (ht : ε ≤ t) :
    |Real.exp (-k * t) - Real.exp (-k * s)| ≤ ε⁻¹ * |t - s| := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (-k * y))
      (-k * Real.exp (-k * x)) x := by
    convert! (((hasDerivAt_id x).const_mul (-k)).exp) using 1 <;> simp <;> ring
  have hb (x : ℝ) (hx : x ∈ Ici ε) : ‖-k * Real.exp (-k * x)‖ ≤ ε⁻¹ := by
    rw [norm_mul, norm_neg, Real.norm_of_nonneg hk.le,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact scalar_exponential_rate_bound hk hε hx
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x (_ : x ∈ Ici ε) => (hd x).hasDerivWithinAt) hb
      (convex_Ici ε) hs ht

/-- The real bounded diagonal exponential operator, with no upper bound
on its positive rates. -/
def spectralPoissonKernel {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (t : ℝ) :
    SpectralSpace ι →L[ℝ] SpectralSpace ι :=
  spectralDiagonal (fun i => Real.exp (-k i * |t|))
    (Real.exp_pos (-k₀ * |t|)).le (fun i => by
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      nlinarith only [hk i, abs_nonneg t])

@[simp] theorem spectralPoissonKernel_apply {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (t : ℝ) (u : SpectralSpace ι) (i : ι) :
    spectralPoissonKernel k hk₀ hk t u i = Real.exp (-k i * |t|) * u i := rfl

theorem spectralPoissonKernel_norm_le {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (t : ℝ) :
    ‖spectralPoissonKernel k hk₀ hk t‖ ≤ Real.exp (-k₀ * |t|) :=
  spectralDiagonal_norm_le _ _ _

theorem spectralPoissonKernel_norm_sub_le_away_zero {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) {ε s t : ℝ}
    (hε : 0 < ε) (hs : ε ≤ |s|) (ht : ε ≤ |t|) :
    ‖spectralPoissonKernel k hk₀ hk t - spectralPoissonKernel k hk₀ hk s‖ ≤
      ε⁻¹ * |t - s| := by
  have hb (i : ι) : |Real.exp (-k i * |t|) - Real.exp (-k i * |s|)| ≤
      ε⁻¹ * |t - s| :=
    (scalar_exponential_lipschitz_away_zero (hk₀.trans_le (hk i)) hε hs ht).trans
      (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le t s) (inv_nonneg.mpr hε.le))
  let D := spectralDiagonal (fun i => Real.exp (-k i * |t|) - Real.exp (-k i * |s|))
    (mul_nonneg (inv_nonneg.mpr hε.le) (abs_nonneg _)) hb
  have he : spectralPoissonKernel k hk₀ hk t - spectralPoissonKernel k hk₀ hk s = D := by
    ext u i
    change Real.exp (-k i * |t|) * u i - Real.exp (-k i * |s|) * u i =
      (Real.exp (-k i * |t|) - Real.exp (-k i * |s|)) * u i
    ring
  rw [he]
  exact spectralDiagonal_norm_le _ _ _

theorem spectralPoissonKernel_continuousAt {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt (spectralPoissonKernel k hk₀ hk) t := by
  have he : 0 < |t| / 2 := half_pos (abs_pos.mpr ht)
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min (|t| / 2) (ε * (|t| / 2)), lt_min he (mul_pos hε he), ?_⟩
  intro s hs
  rw [Real.dist_eq] at hs
  have hs₁ := (lt_min_iff.mp hs).1
  have hs₂ := (lt_min_iff.mp hs).2
  have hab := abs_abs_sub_abs_le t s
  have hsl : |t| / 2 ≤ |s| := by
    rw [abs_sub_comm t s] at hab
    have hts := (le_abs_self (|t| - |s|)).trans hab
    linarith
  rw [dist_eq_norm]
  calc
    _ ≤ (|t| / 2)⁻¹ * |s - t| :=
      spectralPoissonKernel_norm_sub_le_away_zero k hk₀ hk he
        (by linarith only [abs_nonneg t]) hsl
    _ < (|t| / 2)⁻¹ * (ε * (|t| / 2)) :=
      mul_lt_mul_of_pos_left hs₂ (inv_pos.mpr he)
    _ = ε := by field_simp

/-- This is exp(-delta t) times the actual signed derivative of the
full-line Green kernel, with the harmless value at zero chosen explicitly. -/
def weightedSpectralFirstDerivativeKernel {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (δ t : ℝ) :
    SpectralSpace ι →L[ℝ] SpectralSpace ι :=
  Real.exp (-δ * t) •
    ((if 0 ≤ t then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) • spectralPoissonKernel k hk₀ hk t)

theorem weightedSpectralFirstDerivativeKernel_apply {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (δ t : ℝ) (u : SpectralSpace ι) (i : ι) :
    weightedSpectralFirstDerivativeKernel k hk₀ hk δ t u i =
      Real.exp (-δ * t) * (if 0 ≤ t then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) *
        Real.exp (-k i * |t|) * u i := by
  change Real.exp (-δ * t) *
    ((if 0 ≤ t then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) *
      (Real.exp (-k i * |t|) * u i)) = _
  ring

theorem weightedSpectralFirstDerivativeKernel_norm_le {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (δ t : ℝ) :
    ‖weightedSpectralFirstDerivativeKernel k hk₀ hk δ t‖ ≤ k₀ * spectralMajorant k₀ δ t := by
  have hc : ‖if 0 ≤ t then (1 / 2 : ℝ) else -(1 / 2 : ℝ)‖ = 1 / 2 := by
    split_ifs <;> norm_num
  rw [weightedSpectralFirstDerivativeKernel, norm_smul, norm_smul,
    Real.norm_of_nonneg (Real.exp_pos _).le, hc]
  calc
    _ ≤ Real.exp (-δ * t) * ((1 / 2) * Real.exp (-k₀ * |t|)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (spectralPoissonKernel_norm_le k hk₀ hk t) (by norm_num))
        (Real.exp_pos _).le
    _ = k₀ * spectralMajorant k₀ δ t := by
      unfold spectralMajorant
      rw [sub_eq_add_neg, Real.exp_add]
      field_simp
      <;> ring

theorem weightedSpectralFirstDerivativeKernel_continuousAt {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (δ : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt (weightedSpectralFirstDerivativeKernel k hk₀ hk δ) t := by
  have hP := spectralPoissonKernel_continuousAt k hk₀ hk ht
  have hexp : ContinuousAt (fun s : ℝ => Real.exp (-δ * s)) t := by fun_prop
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · apply (hexp.smul (hP.const_smul (-(1 / 2 : ℝ)))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hneg] with s hs
    simp only [weightedSpectralFirstDerivativeKernel, Pi.smul_apply,
      if_neg (not_le.mpr (show s < 0 from hs))]
    rfl
  · apply (hexp.smul (hP.const_smul (1 / 2 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hpos] with s hs
    simp only [weightedSpectralFirstDerivativeKernel, Pi.smul_apply,
      if_pos (show 0 ≤ s from (show 0 < s from hs).le)]
    rfl

theorem weightedSpectralFirstDerivativeKernel_integrable {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀) :
    Integrable (weightedSpectralFirstDerivativeKernel k hk₀ hk δ) := by
  have hc : ContinuousOn (weightedSpectralFirstDerivativeKernel k hk₀ hk δ) ({0}ᶜ : Set ℝ) :=
    fun t ht => (weightedSpectralFirstDerivativeKernel_continuousAt k hk₀ hk δ
      (by simpa only [mem_compl_iff, mem_singleton_iff] using ht)).continuousWithinAt
  have hm : AEStronglyMeasurable (weightedSpectralFirstDerivativeKernel k hk₀ hk δ)
      (volume : Measure ℝ) := by
    simpa only [restrict_compl_singleton] using
      hc.aestronglyMeasurable (μ := volume) (measurableSet_singleton 0).compl
  exact ((spectralMajorant_integral hk₀ hδ).1.const_mul k₀).mono' hm
    (Eventually.of_forall (weightedSpectralFirstDerivativeKernel_norm_le k hk₀ hk δ))

#print axioms spectralPoissonKernel_continuousAt
#print axioms weightedSpectralFirstDerivativeKernel_integrable

end Yamabe3.Analysis.Delaunay
