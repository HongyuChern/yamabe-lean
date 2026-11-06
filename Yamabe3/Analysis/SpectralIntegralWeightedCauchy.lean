import Yamabe3.Analysis.SpectralFirstDerivativeConvolution
import Yamabe3.Analysis.SpectralIntegralPotentialInverse

/-!
# Strong weighted Cauchy bounds for the actual integral-potential fixed point

The fixed point remains exactly the existing spectralIntegralPotentialInverse.
Its forcing inside the free resolvent is literally F - V smul w.  The
first derivative uses the real Bochner derivative kernel proved above.
The constants depend only on the spectral lower rate, weight, integrated
contraction parameter and bounded potential, before the source and time.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000

open Set Filter MeasureTheory
open scoped Topology lp BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

theorem spectralIntegralPotentialInverse_weighted_hasDerivAt {ι : Type*}
    (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) :
    let w := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F
    HasDerivAt (fun s => Real.exp (δ * s) • w s)
      (Real.exp (δ * t) • spectralFirstDerivativeConvolution k hk₀ hk δ (F - V • w) t) t := by
  dsimp only
  let w := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F
  have heq : (fun s => Real.exp (δ * s) • spectralResolvent k hk₀ hk hδ (F - V • w) s) =
      fun s => Real.exp (δ * s) • w s := by
    funext s
    exact congrArg (fun f : ℝ →ᵇ SpectralSpace ι => Real.exp (δ * s) • f s)
      (spectralIntegralPotentialInverse_fixed k hk₀ hk hδ hκ0 hκ1 V hV F)
  have h := spectralResolvent_weighted_hasDerivAt k hk₀ hk hδ (F - V • w) t
  rw [heq] at h
  exact h

theorem spectralIntegralPotentialInverse_weighted_cauchy_bound {ι : Type*}
    (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ)
    (F : ℝ →ᵇ SpectralSpace ι) :
    let w := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F
    let U := fun t => Real.exp (δ * t) • w t
    Differentiable ℝ U ∧ ∀ t : ℝ,
      ‖U t‖ ≤ ((1 / ((k₀ ^ 2 - δ ^ 2) * (1 - κ))) * ‖F‖) * Real.exp (δ * t) ∧
      ‖deriv U t‖ ≤
        ((k₀ / (k₀ ^ 2 - δ ^ 2)) *
          (1 + ‖V‖ / ((k₀ ^ 2 - δ ^ 2) * (1 - κ))) * ‖F‖) * Real.exp (δ * t) := by
  dsimp only
  let w := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F
  have hgap := spectral_gap_positive hk₀ hδ
  have hκ := sub_pos.mpr hκ1
  have hwn := spectralIntegralPotentialInverse_norm_le k hk₀ hk hδ hκ0 hκ1 V hV F
  have hsource : ‖F - V • w‖ ≤ ‖F‖ + ‖V‖ * ((‖F‖ / (k₀ ^ 2 - δ ^ 2)) / (1 - κ)) := by
    calc
      _ ≤ ‖F‖ + ‖V • w‖ := norm_sub_le _ _
      _ ≤ ‖F‖ + ‖V‖ * ‖w‖ := add_le_add le_rfl (norm_smul_le V w)
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hwn (norm_nonneg V))
  refine ⟨fun t => (spectralIntegralPotentialInverse_weighted_hasDerivAt
    k hk₀ hk hδ hκ0 hκ1 V hV F t).differentiableAt, ?_⟩
  intro t
  constructor
  · rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      _ ≤ Real.exp (δ * t) * ((‖F‖ / (k₀ ^ 2 - δ ^ 2)) / (1 - κ)) :=
        mul_le_mul_of_nonneg_left ((w.norm_coe_le_norm t).trans hwn) (Real.exp_pos _).le
      _ = _ := by field_simp <;> ring
  · rw [(spectralIntegralPotentialInverse_weighted_hasDerivAt
      k hk₀ hk hδ hκ0 hκ1 V hV F t).deriv,
      norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      _ ≤ Real.exp (δ * t) * (k₀ * ‖F - V • w‖ / (k₀ ^ 2 - δ ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (spectralFirstDerivativeConvolution_norm_le k hk₀ hk hδ (F - V • w) t)
          (Real.exp_pos _).le
      _ ≤ Real.exp (δ * t) *
          (k₀ * (‖F‖ + ‖V‖ * ((‖F‖ / (k₀ ^ 2 - δ ^ 2)) / (1 - κ))) /
            (k₀ ^ 2 - δ ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsource hk₀.le) hgap.le)
          (Real.exp_pos _).le
      _ = _ := by field_simp <;> ring

/-- Coordinate derivatives are evaluations of this very strong Hilbert
derivative, rather than separately selected scalar solution derivatives. -/
theorem spectralIntegralPotentialInverse_weighted_derivative_coordinate {ι : Type*}
    (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) (i : ι) :
    let U := fun s => Real.exp (δ * s) •
      spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F s
    deriv (fun s => U s i) t = deriv U t i := by
  dsimp only
  let U := fun s => Real.exp (δ * s) •
    spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F s
  let ev := lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i
  have hd := spectralIntegralPotentialInverse_weighted_hasDerivAt k hk₀ hk hδ hκ0 hκ1 V hV F t
  have he := (ev.hasFDerivAt.comp_hasDerivAt t hd).deriv
  change deriv (ev ∘ U) t = ev (deriv U t)
  rw [he, hd.deriv]

#print axioms spectralIntegralPotentialInverse_weighted_hasDerivAt
#print axioms spectralIntegralPotentialInverse_weighted_cauchy_bound
#print axioms spectralIntegralPotentialInverse_weighted_derivative_coordinate

end Yamabe3.Analysis.Delaunay
