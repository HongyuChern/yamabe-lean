import Yamabe3.Analysis.Green.RegularizedNewton
import Yamabe3.Analysis.Green.CutoffNewtonLimits

/-!
# Newton-kernel point evaluation for integrable locally continuous multipliers

The previously proved 4π approximate identity is extended from globally
bounded continuous functions to genuine L1 functions continuous only at the
pole. The uncontrolled part vanishes on a fixed ball and is handled by an
integrable tail bound. This permits another Green pole away from the point
being evaluated; global boundedness is not imposed on that Green function.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace Yamabe3.RegularizedNewton

/-- For every positive regularization width the actual Newton kernel is
bounded globally, so multiplying a genuine L1 function remains integrable. -/
theorem kernel_uniform_bound {ε : ℝ} (hε : 0 < ε) (x : E) :
    ‖kernel ε x‖ ≤ 3 * ε ^ 2 * (ε ^ 5)⁻¹ := by
  rw [Real.norm_of_nonneg (kernel_nonneg hε x)]
  unfold kernel
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [add_comm, Nat.cast_ofNat] using radial_rpow_le_inv_pow ‖x‖ hε 5

theorem integrable_kernel_mul_L1 {f : E → ℝ} (hf : Integrable f)
    {ε : ℝ} (hε : 0 < ε) : Integrable (fun x => kernel ε x * f x) := by
  apply (hf.norm.const_mul (3 * ε ^ 2 * (ε ^ 5)⁻¹)).mono'
  · exact (contDiff_kernel hε).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (kernel_uniform_bound hε x) (norm_nonneg _)

/-- Rescaling and dominated convergence need measurability globally and
continuity only at the evaluation point. -/
theorem tendsto_kernel_test_of_measurable_bounded {f : E → ℝ}
    (hf : Measurable f) (hc : ContinuousAt f 0) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun ε : ℝ => ∫ x : E, kernel ε x * f x) (𝓝[>] 0)
      (𝓝 (4 * Real.pi * f 0)) := by
  have hdom : Tendsto (fun ε : ℝ => ∫ y : E, kernel 1 y * f (ε • y)) (𝓝 0)
      (𝓝 (∫ y : E, kernel 1 y * f 0)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun y : E => kernel 1 y * C)
    · exact Eventually.of_forall fun ε =>
        (contDiff_kernel (by norm_num : (0 : ℝ) < 1)).continuous.aestronglyMeasurable.mul
          (hf.comp (continuous_const_smul ε).measurable).aestronglyMeasurable
    · exact Eventually.of_forall fun ε => Eventually.of_forall fun y => by
        rw [norm_mul, Real.norm_of_nonneg (kernel_nonneg (by norm_num) y)]
        exact mul_le_mul_of_nonneg_left (hC _) (kernel_nonneg (by norm_num) y)
    · exact (integrable_kernel (by norm_num : (0 : ℝ) < 1)).mul_const C
    · exact Eventually.of_forall fun y => by
        have hy : Tendsto (fun ε : ℝ => ε • y) (𝓝 0) (𝓝 (0 : E)) := by
          have hyc : Continuous (fun ε : ℝ => ε • y) := by fun_prop
          simpa using hyc.tendsto (0 : ℝ)
        exact tendsto_const_nhds.mul (hc.tendsto.comp hy)
  have hlim : Tendsto (fun ε : ℝ => ∫ y : E, kernel 1 y * f (ε • y)) (𝓝 0)
      (𝓝 (4 * Real.pi * f 0)) := by
    simpa only [integral_mul_const, integral_kernel (by norm_num : (0 : ℝ) < 1)] using hdom
  apply (hlim.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_kernel_mul_eq_rescaled hε f).symm

/-- An integrable multiplier vanishing near the pole has vanishing kernel
pairings. Its behavior away from the pole may be unbounded. -/
theorem tendsto_kernel_test_zero_of_L1_zero_near {f : E → ℝ}
    (hf : Integrable f) {r : ℝ} (hr : 0 < r)
    (hz : ∀ x : E, ‖x‖ < r → f x = 0) :
    Tendsto (fun ε : ℝ => ∫ x : E, kernel ε x * f x) (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun ε : ℝ => ∫ x : E, kernel ε x * f x) (𝓝[>] 0)
      (𝓝 (∫ _ : E, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x : E => 3 * (r ^ 5)⁻¹ * ‖f x‖)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (contDiff_kernel hε).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable
    · have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 :=
        nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
      filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hε1
      change 0 < ε at hε
      exact Eventually.of_forall fun x => by
        by_cases hx : ‖x‖ < r
        · simp only [hz x hx, mul_zero, norm_zero, le_refl]
        · have hp : (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) ≤ (r ^ 5)⁻¹ := by
            simpa using annular_radial_power_bound hr (le_of_not_gt hx) ε 5
          have hεsq : ε ^ 2 ≤ 1 := by nlinarith
          have hk : kernel ε x ≤ 3 * (r ^ 5)⁻¹ := by
            unfold kernel
            calc
              _ ≤ (3 * ε ^ 2) * (r ^ 5)⁻¹ :=
                mul_le_mul_of_nonneg_left hp (by positivity)
              _ ≤ _ := by nlinarith [inv_nonneg.mpr (pow_nonneg hr.le 5)]
          rw [norm_mul, Real.norm_of_nonneg (kernel_nonneg hε x)]
          exact mul_le_mul_of_nonneg_right hk (norm_nonneg _)
    · exact hf.norm.const_mul _
    · exact Eventually.of_forall fun x => by
        by_cases hx : x = 0
        · have hf0 : f x = 0 := hz x (by simpa [hx] using hr)
          simp only [hf0, mul_zero]
          exact tendsto_const_nhds
        · have hk : Tendsto (fun ε : ℝ => kernel ε x) (𝓝 0) (𝓝 (0 : ℝ)) := by
            have h := ((tendsto_id.pow 2).const_mul (3 : ℝ)).mul
              (tendsto_radial_power hx 5)
            simpa only [kernel, id_eq, Nat.cast_ofNat, zero_pow (by decide : (2 : ℕ) ≠ 0),
              mul_zero, zero_mul] using h
          simpa only [zero_mul] using
            (hk.mono_left nhdsWithin_le_nhds).mul_const (f x)
  simpa only [integral_zero] using hlim

/-- The actual normalized Newton kernel evaluates every genuine L1
function continuous at the pole; no boundedness away from that pole is used. -/
theorem tendsto_kernel_test_of_L1_continuousAt {f : E → ℝ}
    (hf : Integrable f) (hm : Measurable f) (hc : ContinuousAt f 0) :
    Tendsto (fun ε : ℝ => ∫ x : E, kernel ε x * f x) (𝓝[>] 0)
      (𝓝 (4 * Real.pi * f 0)) := by
  have hevent : ∀ᶠ x in 𝓝 (0 : E), ‖f x‖ < ‖f 0‖ + 1 :=
    hc.norm.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let f₀ : E → ℝ := (ball 0 r).indicator f
  let f₁ : E → ℝ := fun x => f x - f₀ x
  have hf₀ : Integrable f₀ := hf.indicator measurableSet_ball
  have hf₁ : Integrable f₁ := hf.sub hf₀
  have heq : f₀ =ᶠ[𝓝 (0 : E)] f := by
    filter_upwards [ball_mem_nhds (0 : E) hr] with x hx
    exact indicator_of_mem hx f
  have hf₀c : ContinuousAt f₀ 0 := hc.congr_of_eventuallyEq heq
  have hbounded (x : E) : ‖f₀ x‖ ≤ ‖f 0‖ + 1 := by
    by_cases hx : x ∈ ball 0 r
    · rw [show f₀ x = f x from indicator_of_mem hx f]
      exact (hball hx).le
    · rw [show f₀ x = 0 from indicator_of_notMem hx f, norm_zero]
      positivity
  have h₀ := tendsto_kernel_test_of_measurable_bounded (f := f₀)
    (hm.indicator measurableSet_ball) hf₀c hbounded
  have h₁ := tendsto_kernel_test_zero_of_L1_zero_near hf₁ hr (by
    intro x hx
    have hxball : x ∈ ball (0 : E) r := by simpa using hx
    change f x - (ball 0 r).indicator f x = 0
    rw [indicator_of_mem hxball, sub_self])
  have hsum := h₀.add h₁
  have hzero : f₀ 0 = f 0 := heq.eq_of_nhds
  rw [hzero, add_zero] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [← integral_add (integrable_kernel_mul_L1 hf₀ hε) (integrable_kernel_mul_L1 hf₁ hε)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by dsimp [f₁]; ring

#print axioms kernel_uniform_bound
#print axioms integrable_kernel_mul_L1
#print axioms tendsto_kernel_test_of_measurable_bounded
#print axioms tendsto_kernel_test_zero_of_L1_zero_near
#print axioms tendsto_kernel_test_of_L1_continuousAt

end Yamabe3.RegularizedNewton
