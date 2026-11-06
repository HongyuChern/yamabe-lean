import PoincareLib.Geometry.Riemannian.Heat.Energy.PositivePart

/-!
# Quantitative smooth positive-part approximations for native energy tests

The approximation is the explicit scaled primitive of the actual smooth
transition from the fixed upstream library. Its uniform error and derivative
bounds provide the scalar input to the coercive negative-part argument; no
H1 lattice or weak negative-part derivative is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Yamabe3.Analysis.GreenPositivity

open Poincare.Analysis.Heat

/-- Past one the transition is exactly one; integrating that literal
identity gives the uniform one-unit approximation error. -/
theorem sub_one_le_smoothPositivePart (t : ℝ) :
    t - 1 ≤ smoothPositivePart t := by
  by_cases ht : 1 ≤ t
  · have htail : (∫ z in (1 : ℝ)..t, Real.smoothTransition z) = t - 1 := by
      calc
        _ = ∫ _ in (1 : ℝ)..t, (1 : ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le ht
          intro z hz
          exact Real.smoothTransition.one_of_one_le hz.1.le
        _ = _ := by simp
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (Real.smoothTransition.continuous.intervalIntegrable (0 : ℝ) 1)
      (Real.smoothTransition.continuous.intervalIntegrable (1 : ℝ) t)
    rw [htail] at hsplit
    change smoothPositivePart 1 + (t - 1) = smoothPositivePart t at hsplit
    linarith [smoothPositivePart_nonneg 1]
  · linarith [smoothPositivePart_nonneg t]

theorem smoothPositivePart_gap_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t - smoothPositivePart t ∧ t - smoothPositivePart t ≤ 1 := by
  have hupper := smoothPositivePart_le_posPart t
  rw [max_eq_left ht] at hupper
  constructor <;> linarith [sub_one_le_smoothPositivePart t]

/-- The actual smooth approximation to the positive part, with width δ. -/
def smoothPositiveApprox (δ t : ℝ) : ℝ := δ * smoothPositivePart (t / δ)

theorem contDiff_smoothPositiveApprox (δ : ℝ) :
    ContDiff ℝ ∞ (smoothPositiveApprox δ) :=
  contDiff_const.mul (contDiff_smoothPositivePart.comp (contDiff_id.div_const δ))

theorem smoothPositiveApprox_nonneg {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    0 ≤ smoothPositiveApprox δ t := mul_nonneg hδ.le (smoothPositivePart_nonneg _)

theorem smoothPositiveApprox_eq_zero_of_nonpos {δ t : ℝ} (hδ : 0 < δ)
    (ht : t ≤ 0) : smoothPositiveApprox δ t = 0 := by
  unfold smoothPositiveApprox
  rw [smoothPositivePart_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ht hδ.le), mul_zero]

theorem smoothPositiveApprox_eq_zero_iff {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    smoothPositiveApprox δ t = 0 ↔ t ≤ 0 := by
  rw [smoothPositiveApprox, mul_eq_zero, or_iff_right hδ.ne', smoothPositivePart_eq_zero_iff]
  rw [div_le_iff₀ hδ, zero_mul]

/-- The exact global approximation error, including the nonpositive side. -/
theorem posPart_sub_smoothPositiveApprox_bounds {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    0 ≤ max t 0 - smoothPositiveApprox δ t ∧
      max t 0 - smoothPositiveApprox δ t ≤ δ := by
  by_cases ht : t ≤ 0
  · rw [max_eq_right ht, smoothPositiveApprox_eq_zero_of_nonpos hδ ht]
    rw [sub_self]
    exact ⟨le_rfl, hδ.le⟩
  · have ht0 : 0 ≤ t := (lt_of_not_ge ht).le
    have hgap := smoothPositivePart_gap_bounds (div_nonneg ht0 hδ.le)
    have hid : t - smoothPositiveApprox δ t =
        δ * (t / δ - smoothPositivePart (t / δ)) := by
      unfold smoothPositiveApprox
      field_simp [hδ.ne']
    rw [max_eq_left ht0, hid]
    refine ⟨mul_nonneg hδ.le hgap.1, ?_⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hgap.2 hδ.le

theorem smoothPositiveApprox_le_posPart {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    smoothPositiveApprox δ t ≤ max t 0 :=
  sub_nonneg.mp (posPart_sub_smoothPositiveApprox_bounds hδ t).1

/-- Scaling cancels in the first derivative, leaving the genuine transition. -/
theorem hasDerivAt_smoothPositiveApprox {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (smoothPositiveApprox δ) (Real.smoothTransition (t / δ)) t := by
  convert! (((hasDerivAt_smoothPositivePart (t / δ)).comp t
    ((hasDerivAt_id t).div_const δ)).const_mul δ) using 1
  field_simp [hδ.ne']

theorem deriv_smoothPositiveApprox {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    deriv (smoothPositiveApprox δ) t = Real.smoothTransition (t / δ) :=
  (hasDerivAt_smoothPositiveApprox hδ t).deriv

theorem deriv_smoothPositiveApprox_bounds {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    0 ≤ deriv (smoothPositiveApprox δ) t ∧ deriv (smoothPositiveApprox δ) t ≤ 1 := by
  rw [deriv_smoothPositiveApprox hδ]
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem deriv_smoothPositiveApprox_sq_le {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    (deriv (smoothPositiveApprox δ) t) ^ 2 ≤ deriv (smoothPositiveApprox δ) t := by
  obtain ⟨h₀, h₁⟩ := deriv_smoothPositiveApprox_bounds hδ t
  simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left h₁ h₀

/-- The signed-potential error in the native energy comparison is bounded
by δ times the actual nonnegative approximation. -/
theorem smoothPositiveApprox_potential_gap {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    0 ≤ t * smoothPositiveApprox δ t - (smoothPositiveApprox δ t) ^ 2 ∧
      t * smoothPositiveApprox δ t - (smoothPositiveApprox δ t) ^ 2 ≤
        δ * smoothPositiveApprox δ t := by
  by_cases ht : t ≤ 0
  · rw [smoothPositiveApprox_eq_zero_of_nonpos hδ ht]
    norm_num
  · have ht0 : 0 ≤ t := (lt_of_not_ge ht).le
    have hgap := posPart_sub_smoothPositiveApprox_bounds hδ t
    rw [max_eq_left ht0] at hgap
    have hnonneg := smoothPositiveApprox_nonneg hδ t
    have hid : t * smoothPositiveApprox δ t - (smoothPositiveApprox δ t) ^ 2 =
        (t - smoothPositiveApprox δ t) * smoothPositiveApprox δ t := by ring
    rw [hid]
    exact ⟨mul_nonneg hgap.1 hnonneg,
      mul_le_mul_of_nonneg_right hgap.2 hnonneg⟩

/-- Pointwise approximation follows from the proved uniform error bound. -/
theorem tendsto_smoothPositiveApprox (t : ℝ) :
    Tendsto (fun δ : ℝ => smoothPositiveApprox δ t) (𝓝[>] 0) (𝓝 (max t 0)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hevent : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < ε :=
    nhdsWithin_le_nhds (Iio_mem_nhds hε)
  filter_upwards [self_mem_nhdsWithin, hevent] with δ hδ hδε
  have hgap := posPart_sub_smoothPositiveApprox_bounds hδ t
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg hgap.1]
  exact hgap.2.trans_lt hδε

end Yamabe3.Analysis.GreenPositivity
