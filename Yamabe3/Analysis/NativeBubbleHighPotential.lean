import Yamabe3.Analysis.NativeHighCoupledDtN
import Yamabe3.Analysis.DelaunayKernelPeriodBound
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The literal full-bubble cylinder potential, including its integrated
weight-two bound. The density below is sech(t)^2 in exponential form.
The full-line integral is actually proved, not an assumed mass bound. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

def fullBubbleDensity (t : ℝ) : ℝ := 4 * Real.exp (2*t) / (1 + Real.exp (2*t))^2

theorem fullBubbleDensity_continuous : Continuous fullBubbleDensity := by
  unfold fullBubbleDensity
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  exact pow_ne_zero _ (ne_of_gt (by positivity : 0 < 1 + Real.exp (2*t)))

theorem fullBubbleDensity_bounds (t : ℝ) : 0 ≤ fullBubbleDensity t ∧ fullBubbleDensity t ≤ 1 := by
  have he := Real.exp_pos (2*t)
  unfold fullBubbleDensity
  refine ⟨by positivity, ?_⟩
  apply (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < 1 + Real.exp (2*t)))).mpr
  nlinarith only [sq_nonneg (Real.exp (2*t)-1)]

private theorem bubble_majorant (t : ℝ) : fullBubbleDensity t ≤ 16 * spectralMajorant 2 0 t := by
  have he := Real.exp_pos (2*t)
  unfold fullBubbleDensity spectralMajorant
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    simp only [neg_zero, zero_mul, zero_sub, Real.exp_neg]
    have h : 4 * Real.exp (2*t) / (1+Real.exp (2*t))^2 ≤ 4 / Real.exp (2*t) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos (by positivity : 0 < 1+Real.exp (2*t))) he).mpr
      nlinarith only [he]
    convert h using 1 <;> ring
  · rw [abs_of_nonpos (le_of_not_ge ht)]
    simp only [neg_zero, zero_mul, zero_sub, mul_neg, neg_neg]
    have h : 4 * Real.exp (2*t) / (1+Real.exp (2*t))^2 ≤ 4 * Real.exp (2*t) := by
      apply (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < 1+Real.exp (2*t)))).mpr
      nlinarith only [he, sq_nonneg (Real.exp (2*t)), mul_nonneg he.le (sq_nonneg (Real.exp (2*t)))]
    convert h using 1 <;> ring

theorem fullBubbleDensity_integrable : Integrable fullBubbleDensity := by
  have hm := ((spectralMajorant_integral (k₀ := (2:ℝ)) (δ := (0:ℝ))
    (by norm_num) (by norm_num)).1).const_mul 16
  apply hm.mono' fullBubbleDensity_continuous.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    rw [Real.norm_of_nonneg (fullBubbleDensity_bounds t).1]
    exact bubble_majorant t

private def bubblePrimitive (t : ℝ) : ℝ := 2 * Real.exp (2*t) / (1+Real.exp (2*t))

private theorem bubblePrimitive_derivative (t : ℝ) :
    HasDerivAt bubblePrimitive (fullBubbleDensity t) t := by
  have he := ((hasDerivAt_id t).const_mul 2).exp
  have h := (he.const_mul 2).div ((hasDerivAt_const t (1:ℝ)).add he)
    (ne_of_gt (by positivity : 0 < 1 + Real.exp (2*t)))
  apply h.congr_deriv
  dsimp only [fullBubbleDensity, id_eq, Pi.add_apply]
  ring

private theorem bubblePrimitive_bot : Tendsto bubblePrimitive atBot (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (2*t)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_pos (by norm_num : (0:ℝ) < 2)).2 tendsto_id)
  have h := (he.const_mul 2).div (tendsto_const_nhds.add he) (by norm_num : (1:ℝ)+0 ≠ 0)
  change Tendsto bubblePrimitive atBot (𝓝 ((2:ℝ)*0/(1+0))) at h
  norm_num at h
  exact h

private theorem bubblePrimitive_top : Tendsto bubblePrimitive atTop (𝓝 2) := by
  have he : Tendsto (fun t : ℝ => Real.exp (2*t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ) < 2)).2 tendsto_id)
  have hh : Tendsto (fun t : ℝ => (1+Real.exp (2*t))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_const_nhds.add_atTop he)
  have h : Tendsto (fun t : ℝ => 2 - 2 * (1+Real.exp (2*t))⁻¹) atTop (𝓝 (2 - 2*0)) := tendsto_const_nhds.sub (hh.const_mul 2)
  have hf : bubblePrimitive = fun t : ℝ => 2 - 2 * (1+Real.exp (2*t))⁻¹ := by
    funext t
    unfold bubblePrimitive
    field_simp
    <;> ring
  rw [hf]
  simpa only [mul_zero, sub_zero] using h

theorem fullBubbleDensity_mass : (∫ t : ℝ, fullBubbleDensity t) = 2 := by
  simpa only [sub_zero] using integral_of_hasDerivAt_of_tendsto
    bubblePrimitive_derivative fullBubbleDensity_integrable bubblePrimitive_bot bubblePrimitive_top

/-- Threshold integration on the whole line retains the true mass two. -/
theorem weightTwo_integrable_density_bound (p : ℝ → ℝ) (hp : Continuous p)
    (hb : ∀ s, 0 ≤ p s ∧ p s ≤ 1) (hi : Integrable p) (hm : (∫ s : ℝ, p s) ≤ 2) :
    (3/4) * (∫ s : ℝ, futureWeightTwoKernel s * p s) ≤
      (5/3) * (1-weightTwoThreshold) := by
  have hk : Integrable (fun s => futureWeightTwoKernel s * p s) := by
    apply futureWeightTwoKernel_integrable.mono' (futureWeightTwoKernel_continuous.mul hp).aestronglyMeasurable
    exact Eventually.of_forall fun s => by
      change ‖futureWeightTwoKernel s * p s‖ ≤ futureWeightTwoKernel s
      rw [Real.norm_of_nonneg (mul_nonneg (futureWeightTwoKernel_nonneg s) (hb s).1)]
      exact mul_le_of_le_one_right (futureWeightTwoKernel_nonneg s) (hb s).2
  have h := integral_mono hk ((hi.const_mul weightTwoThreshold).add weightTwoExcess_integrable)
    (fun s => weightTwo_threshold_pointwise (hb s).1 (hb s).2)
  simp only [Pi.add_apply] at h
  rw [integral_add (hi.const_mul weightTwoThreshold) weightTwoExcess_integrable,
    integral_const_mul, integral_weightTwoExcess] at h
  have hmul := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-(9/10:ℝ))).le
  change weightTwoThreshold * (∫ s : ℝ, p s) ≤ weightTwoThreshold * 2 at hmul
  nlinarith only [h, hmul]

def fullBubblePhasePotential (τ : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => (15/4) * fullBubbleDensity (t+τ))
    (continuous_const.mul (fullBubbleDensity_continuous.comp (continuous_id.add continuous_const)))
    (15/4) (fun t => by
      rw [Real.norm_of_nonneg (mul_nonneg (by norm_num) (fullBubbleDensity_bounds (t+τ)).1)]
      nlinarith only [(fullBubbleDensity_bounds (t+τ)).2])

theorem fullBubblePhasePotential_kernel (τ t : ℝ) :
    (∫ s : ℝ, spectralMajorant (5/2) (-2) s * |fullBubblePhasePotential τ (t-s)|) ≤
      (5/3) * (1-weightTwoThreshold) := by
  let p := fun s : ℝ => fullBubbleDensity ((t+τ)-s)
  have hi : Integrable p := fullBubbleDensity_integrable.comp_sub_left (t+τ)
  have hm : (∫ s : ℝ, p s) = 2 := by
    rw [show p = fun s => fullBubbleDensity ((t+τ)-s) from rfl,
      integral_sub_left_eq_self, fullBubbleDensity_mass]
  have h := weightTwo_integrable_density_bound p
    (fullBubbleDensity_continuous.comp (continuous_const.sub continuous_id))
    (fun s => fullBubbleDensity_bounds _) hi hm.le
  convert h using 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun s => by
    change spectralMajorant (5/2) (-2) s * |(15/4) * fullBubbleDensity (t-s+τ)| = _
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (fullBubbleDensity_bounds _).1), futureWeightTwoKernel_majorant]
    dsimp only [p]
    rw [show t-s+τ = t+τ-s by ring]
    ring

/-- An actual full-bubble potential instance; all analytic bounds are outputs. -/
def fullBubbleHighPotential (τ : ℝ) : NativeHighPotential where
  κ := (5/3) * (1-weightTwoThreshold)
  κ_nonneg := mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num)))
  κ_lt_one := weightTwo_threshold_gap
  potential := fullBubblePhasePotential τ
  kernel_bound := fullBubblePhasePotential_kernel τ
  nonneg := fun t => mul_nonneg (by norm_num) (fullBubbleDensity_bounds (t+τ)).1
  upper := fun t _ => by
    change (15/4) * fullBubbleDensity (t+τ) ≤ 15/4
    nlinarith only [(fullBubbleDensity_bounds (t+τ)).2]

#print axioms fullBubbleDensity_mass
#print axioms fullBubblePhasePotential_kernel
#print axioms fullBubbleHighPotential
end Yamabe3.Analysis.Delaunay
