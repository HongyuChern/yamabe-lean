import Yamabe3.Analysis.SpectralCoordinateEquation

/-!
# A Hilbert inverse from a true integrated potential bound

The potential is tested against the actual exponential majorant inside
the Bochner convolution. This extends the earlier supremum-smallness
criterion while using the same genuine diagonal resolvent. A later
Delaunay application proves the integrated bound from its actual period
and time mass; no right inverse is assumed here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem spectralMajorant_potential_integrable {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hδ : |δ| < k₀) (V : ℝ →ᵇ ℝ) (t : ℝ) :
    Integrable (fun s : ℝ => spectralMajorant k₀ δ s * |V (t - s)|) := by
  apply ((spectralMajorant_integral hk₀ hδ).1.mul_const ‖V‖).mono'
  · apply Continuous.aestronglyMeasurable
    unfold spectralMajorant
    fun_prop
  · exact Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (spectralMajorant_nonneg hk₀ δ s) (abs_nonneg _))]
      exact mul_le_mul_of_nonneg_left (V.norm_coe_le_norm (t - s))
        (spectralMajorant_nonneg hk₀ δ s)

/-- The integral criterion is an actual aggregate Hilbert norm bound,
obtained before taking any spectral coordinate. -/
theorem spectralResolvent_potential_norm_le {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ : 0 ≤ κ) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ)
    (u : ℝ →ᵇ SpectralSpace ι) :
    ‖spectralResolventCLM k hk₀ hk hδ (V • u)‖ ≤ κ * ‖u‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hκ (norm_nonneg u))).mpr
  intro t
  have hi := (spectralMajorant_potential_integrable hk₀ hδ V t).mul_const ‖u‖
  have hb (s : ℝ) :
      ‖weightedSpectralKernel k hk₀ hk δ s ((V • u) (t - s))‖ ≤
        (spectralMajorant k₀ δ s * |V (t - s)|) * ‖u‖ := by
    calc
      _ ≤ ‖weightedSpectralKernel k hk₀ hk δ s‖ * ‖V (t - s) • u (t - s)‖ :=
        (weightedSpectralKernel k hk₀ hk δ s).le_opNorm _
      _ ≤ spectralMajorant k₀ δ s * (|V (t - s)| * ‖u‖) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (weightedSpectralKernel_norm_le k hk₀ hk δ s)
          (mul_le_mul_of_nonneg_left (u.norm_coe_le_norm _) (abs_nonneg _))
          (by positivity) (spectralMajorant_nonneg hk₀ δ s)
      _ = _ := by ring
  have h := norm_integral_le_of_norm_le hi (Eventually.of_forall hb)
  rw [integral_mul_const] at h
  exact h.trans (mul_le_mul_of_nonneg_right (hV t) (norm_nonneg u))

theorem spectralPotentialIteration_integral_contracting {ι : Type*}
    (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ)
    (F : ℝ →ᵇ SpectralSpace ι) :
    ContractingWith ⟨κ, hκ0⟩ (spectralPotentialIteration k hk₀ hk hδ V F) := by
  refine ⟨hκ1, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro u w
  rw [dist_eq_norm, dist_eq_norm]
  change ‖spectralResolventCLM k hk₀ hk hδ (F - V • u) -
    spectralResolventCLM k hk₀ hk hδ (F - V • w)‖ ≤ κ * ‖u - w‖
  rw [← map_sub]
  have heq : (F - V • u) - (F - V • w) = -(V • (u - w)) := by
    apply BoundedContinuousFunction.ext
    intro t
    change F t - V t • u t - (F t - V t • w t) = -(V t • (u t - w t))
    rw [smul_sub]
    abel
  rw [heq, map_neg, norm_neg]
  exact spectralResolvent_potential_norm_le k hk₀ hk hδ hκ0 V hV (u - w)

/-- A genuine Banach fixed point under the integrated potential criterion. -/
def spectralIntegralPotentialInverse {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ)
    (F : ℝ →ᵇ SpectralSpace ι) : ℝ →ᵇ SpectralSpace ι :=
  (spectralPotentialIteration_integral_contracting k hk₀ hk hδ hκ0 hκ1 V hV F).fixedPoint
    (spectralPotentialIteration k hk₀ hk hδ V F)

theorem spectralIntegralPotentialInverse_fixed {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ)
    (F : ℝ →ᵇ SpectralSpace ι) :
    spectralResolventCLM k hk₀ hk hδ
      (F - V • spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F) =
      spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F :=
  (spectralPotentialIteration_integral_contracting k hk₀ hk hδ hκ0 hκ1 V hV F).fixedPoint_isFixedPt

theorem spectralIntegralPotentialInverse_norm_le {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ)
    (F : ℝ →ᵇ SpectralSpace ι) :
    ‖spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F‖ ≤
      (‖F‖ / (k₀ ^ 2 - δ ^ 2)) / (1 - κ) := by
  let u := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F
  have heq := spectralIntegralPotentialInverse_fixed k hk₀ hk hδ hκ0 hκ1 V hV F
  have hn : ‖u‖ ≤ ‖F‖ / (k₀ ^ 2 - δ ^ 2) + κ * ‖u‖ := by
    calc
      ‖u‖ = ‖spectralResolventCLM k hk₀ hk hδ (F - V • u)‖ := congrArg norm heq.symm
      _ ≤ ‖spectralResolventCLM k hk₀ hk hδ F‖ +
          ‖spectralResolventCLM k hk₀ hk hδ (V • u)‖ := by rw [map_sub]; exact norm_sub_le _ _
      _ ≤ _ := add_le_add (spectralResolvent_norm_le k hk₀ hk hδ F)
        (spectralResolvent_potential_norm_le k hk₀ hk hδ hκ0 V hV u)
  apply (le_div_iff₀ (sub_pos.mpr hκ1)).mpr
  dsimp only [u] at hn ⊢
  nlinarith

/-- Every actual coordinate of the same Hilbert fixed point satisfies the
true conjugated differential equation, by the already proved two-tail FTC. -/
theorem spectralIntegralPotentialInverse_coordinate_equation {ι : Type*}
    (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ)
    (F : ℝ →ᵇ SpectralSpace ι) (i : ι) :
    let u := fun t => spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F t i
    Differentiable ℝ u ∧ Differentiable ℝ (deriv u) ∧
      ∀ t, deriv (deriv u) t = -2 * δ * deriv u t +
        ((k i) ^ 2 - δ ^ 2) * u t + F t i - V t * u t := by
  dsimp only
  let U := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F
  have heq : (fun t => spectralResolvent k hk₀ hk hδ (F - V • U) t i) =
      fun t => U t i := by
    funext t
    exact congrArg (fun H : ℝ →ᵇ SpectralSpace ι => H t i)
      (spectralIntegralPotentialInverse_fixed k hk₀ hk hδ hκ0 hκ1 V hV F)
  have h := spectralResolvent_coordinate_equation k hk₀ hk hδ (F - V • U) i
  dsimp only at h
  rw [heq] at h
  refine ⟨h.1, h.2.1, fun t => ?_⟩
  have he := h.2.2 t
  rw [congrFun heq t] at he
  change deriv (deriv (fun t => U t i)) t = -2 * δ * deriv (fun t => U t i) t +
    ((k i) ^ 2 - δ ^ 2) * U t i + (F t i - V t * U t i) at he
  simpa only [add_sub_assoc] using he

/-- A zero spectral coordinate is preserved by every actual iterate and
therefore by the Banach limit; no separate pointwise-small scalar inverse
is invoked. -/
theorem spectralIntegralPotentialInverse_coordinate_zero {ι : Type*}
    (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ)
    (F : ℝ →ᵇ SpectralSpace ι) (i : ι) (hF : ∀ t, F t i = 0) :
    ∀ t, spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F t i = 0 := by
  let A := spectralPotentialIteration k hk₀ hk hδ V F
  have hc := spectralPotentialIteration_integral_contracting k hk₀ hk hδ hκ0 hκ1 V hV F
  have hz (n : ℕ) : ∀ t, (A^[n] 0) t i = 0 := by
    induction n with
    | zero => intro t; rfl
    | succ n ih =>
      intro t
      rw [Function.iterate_succ_apply']
      change spectralConvolution k hk₀ hk δ (F - V • (A^[n] 0)) t i = 0
      rw [spectralConvolution_coordinate k hk₀ hk hδ]
      have hsrc : (fun s : ℝ => (F - V • (A^[n] 0)) s i) = fun _ => (0 : ℝ) := by
        funext s
        change F s i - V s * (A^[n] 0) s i = 0
        rw [hF, ih, mul_zero, sub_self]
      rw [hsrc]
      simp only [twoRateInverse, leftTail, rightTail, mul_zero, integral_zero, add_zero, zero_div]
  intro t
  have hev : Continuous (fun H : ℝ →ᵇ SpectralSpace ι => H t i) :=
    (lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i).continuous.comp
      (BoundedContinuousFunction.evalCLM ℝ t).continuous
  have hlim := hev.continuousAt.tendsto.comp (hc.tendsto_iterate_fixedPoint 0)
  have hzlim : Tendsto (fun n : ℕ => (A^[n] 0) t i) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hlim hzlim

end Yamabe3.Analysis.Delaunay
