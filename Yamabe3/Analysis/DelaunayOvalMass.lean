import Yamabe3.Analysis.DelaunayOval
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The actual angular mass integral in the small-neck limit

Multiplying the true clock density by the fourth power of the profile
removes the turning-point singularity. The resulting genuine integral
converges to 2 as the squared neck tends to zero. This is an analytic input
to the proposed common-weight-two contraction; no operator bound or actual
periodic time-mass identity is assumed or concluded here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

/-- The actual profile-fourth-power times clock density, after cancellation. -/
def ovalMassDensity (a b θ : ℝ) : ℝ :=
  2 * ovalSquared a b θ * Real.sqrt (ovalSquared a b θ) / Real.sqrt (ovalFactor a b θ)

theorem ovalProfile_four_mul_density {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ : ℝ) :
    ovalProfile a b θ ^ 4 * ovalDensity a b θ = ovalMassDensity a b θ := by
  have hV := (ovalProfile_pos ha hab θ).ne'
  have hK := (Real.sqrt_pos.mpr (ovalFactor_pos ha hab θ)).ne'
  calc
    _ = 2 * ovalProfile a b θ ^ 3 / Real.sqrt (ovalFactor a b θ) := by
      unfold ovalDensity ovalSpeed
      field_simp [hV, hK]
    _ = _ := by
      rw [show ovalProfile a b θ ^ 3 = ovalProfile a b θ ^ 2 * ovalProfile a b θ by ring,
        ovalProfile_sq ha hab]
      unfold ovalMassDensity ovalProfile
      ring

theorem upperSquared_zero : upperSquared 0 = 1 := by
  have h : Real.sqrt (4 : ℝ) = 2 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num
  norm_num [upperSquared, h]

theorem continuous_upperSquared : Continuous upperSquared := by
  unfold upperSquared
  fun_prop

/-- The canceled density is continuous in the neck at zero, including both
turning points; its denominator has the actual nonzero limit sqrt(1+sin²θ). -/
theorem ovalMassDensity_continuousAt_zero (θ : ℝ) :
    ContinuousAt (fun a => ovalMassDensity a (upperSquared a) θ) 0 := by
  have hw : Continuous (fun a => ovalSquared a (upperSquared a) θ) :=
    continuous_id.add ((continuous_upperSquared.sub continuous_id).mul continuous_const)
  have hK : Continuous (fun a => ovalFactor a (upperSquared a) θ) :=
    (hw.add continuous_id).add continuous_upperSquared
  have hK0 : Real.sqrt (ovalFactor 0 (upperSquared 0) θ) ≠ 0 := by
    rw [upperSquared_zero]
    simp only [ovalFactor, ovalSquared, sub_zero, zero_add, one_mul, add_zero]
    exact (Real.sqrt_pos.mpr (by positivity)).ne'
  exact ((continuous_const.mul hw).mul hw.sqrt).continuousAt.div hK.sqrt.continuousAt hK0

/-- One actual common bound for the densities on a punctured neck interval. -/
theorem ovalMassDensity_bound {a : ℝ} (ha : 0 < a) (haq : a < 1 / 4) (θ : ℝ) :
    0 ≤ ovalMassDensity a (upperSquared a) θ ∧ ovalMassDensity a (upperSquared a) θ ≤ 4 := by
  have has : 3 * a ^ 2 < 1 := by nlinarith
  obtain ⟨hab, hb1, _⟩ := upperSquared_properties ha has
  have hsqrt : (3 / 2 : ℝ) ≤ Real.sqrt (4 - 3 * a ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hb0 : (1 / 2 : ℝ) ≤ upperSquared a := by unfold upperSquared; linarith
  have hw := ovalSquared_bounds hab.le θ
  have hw0 : 0 ≤ ovalSquared a (upperSquared a) θ := ha.le.trans hw.1
  have hw1 : ovalSquared a (upperSquared a) θ ≤ 1 := hw.2.trans hb1.le
  have hs1 : Real.sqrt (ovalSquared a (upperSquared a) θ) ≤ 1 := Real.sqrt_le_one.mpr hw1
  have hK : (1 / 2 : ℝ) ≤ Real.sqrt (ovalFactor a (upperSquared a) θ) := by
    apply Real.le_sqrt_of_sq_le
    dsimp only [ovalFactor]
    linarith
  have hKp : 0 < Real.sqrt (ovalFactor a (upperSquared a) θ) := by linarith
  unfold ovalMassDensity
  refine ⟨by positivity, (div_le_iff₀ hKp).mpr ?_⟩
  have hp := mul_le_mul hw1 hs1 (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith

private theorem ovalMass_zero_primitive (θ : ℝ) :
    HasDerivAt (fun s : ℝ => -Real.cos s * Real.sqrt (1 + Real.sin s ^ 2))
      (2 * Real.sin θ ^ 3 / Real.sqrt (1 + Real.sin θ ^ 2)) θ := by
  have hS : 0 < 1 + Real.sin θ ^ 2 := by positivity
  have hroot := (Real.sqrt_pos.mpr hS).ne'
  have hD := (((Real.hasDerivAt_sin θ).pow 2).const_add 1).sqrt hS.ne'
  have h := (Real.hasDerivAt_cos θ).neg.mul hD
  apply h.congr_deriv
  norm_num only [Pi.pow_apply, Pi.neg_apply, Nat.reduceSub, pow_one]
  change - -Real.sin θ * Real.sqrt (1 + Real.sin θ ^ 2) +
      (-Real.cos θ) * (2 * Real.sin θ * Real.cos θ / (2 * Real.sqrt (1 + Real.sin θ ^ 2))) = _
  field_simp [hroot]
  linear_combination Real.sin θ * (Real.sq_sqrt hS.le) -
    Real.sin θ * (Real.sin_sq_add_cos_sq θ)

/-- The exact limiting integral, evaluated with a genuine antiderivative. -/
theorem integral_ovalMassDensity_zero :
    (∫ θ in Icc 0 Real.pi, ovalMassDensity 0 (upperSquared 0) θ) = 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
  have heq : (∫ θ in (0 : ℝ)..Real.pi, ovalMassDensity 0 (upperSquared 0) θ) =
      ∫ θ in (0 : ℝ)..Real.pi, 2 * Real.sin θ ^ 3 / Real.sqrt (1 + Real.sin θ ^ 2) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc (by
      simpa only [uIcc_of_le Real.pi_pos.le] using hθ)
    simp only [ovalMassDensity, upperSquared_zero, ovalSquared, ovalFactor,
      sub_zero, zero_add, one_mul, add_zero, Real.sqrt_sq hs]
    ring
  rw [heq]
  have hc : Continuous (fun θ : ℝ => 2 * Real.sin θ ^ 3 / Real.sqrt (1 + Real.sin θ ^ 2)) :=
    (continuous_const.mul (Real.continuous_sin.pow 3)).div
      (continuous_const.add (Real.continuous_sin.pow 2)).sqrt
      (fun θ => (Real.sqrt_pos.mpr (by positivity)).ne')
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := Real.pi) (fun θ _ => ovalMass_zero_primitive θ)
    (hc.intervalIntegrable _ _)
  norm_num at h
  exact h

/-- The actual angular mass converges to 2 from small positive squared necks.
The proof uses a common integrable bound and true dominated convergence. -/
theorem tendsto_integral_ovalMassDensity_zero :
    Tendsto (fun a : ℝ => ∫ θ in Icc 0 Real.pi, ovalMassDensity a (upperSquared a) θ)
      (𝓝[>] (0 : ℝ)) (𝓝 2) := by
  have hnear : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), 0 < a ∧ a < 1 / 4 := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds] with a ha hq
    exact ⟨ha, hq⟩
  have hm (a : ℝ) : Measurable (ovalMassDensity a (upperSquared a)) := by
    unfold ovalMassDensity ovalFactor ovalSquared
    fun_prop
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Icc 0 Real.pi)) (fun _ : ℝ => (4 : ℝ))
    (F := fun a θ => ovalMassDensity a (upperSquared a) θ)
    (f := ovalMassDensity 0 (upperSquared 0))
    (Eventually.of_forall fun a => (hm a).aestronglyMeasurable)
    (hnear.mono fun a ha => Eventually.of_forall fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ovalMassDensity_bound ha.1 ha.2 θ).1]
      exact (ovalMassDensity_bound ha.1 ha.2 θ).2)
    (integrable_const 4)
    (Eventually.of_forall fun θ => (ovalMassDensity_continuousAt_zero θ).tendsto.mono_left
      nhdsWithin_le_nhds)
  simpa only [integral_ovalMassDensity_zero] using h

end Yamabe3.Analysis.Delaunay
