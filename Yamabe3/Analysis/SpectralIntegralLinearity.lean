import Yamabe3.Analysis.SpectralIntegralPotentialInverse

/-!
# Linearity of the actual integrated-potential Hilbert inverse

The Banach fixed point is unique for each source. Applying that uniqueness
to sums and scalar multiples proves linearity of the already constructed
operator, without selecting new weak solutions. Its genuine aggregate
bound then yields a continuous linear map on C_b(R,lp 2).
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem spectralIntegralPotentialInverse_add {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ)
    (F H : ℝ →ᵇ SpectralSpace ι) :
    spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV (F + H) =
      spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F +
      spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV H := by
  let u := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F
  let w := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV H
  have hfixed : Function.IsFixedPt (spectralPotentialIteration k hk₀ hk hδ V (F + H)) (u + w) := by
    change spectralResolventCLM k hk₀ hk hδ ((F + H) - V • (u + w)) = u + w
    have heq : (F + H) - V • (u + w) = (F - V • u) + (H - V • w) := by
      apply BoundedContinuousFunction.ext
      intro t
      change F t + H t - V t • (u t + w t) = (F t - V t • u t) + (H t - V t • w t)
      rw [smul_add]
      abel
    rw [heq, map_add,
      spectralIntegralPotentialInverse_fixed k hk₀ hk hδ hκ0 hκ1 V hV F,
      spectralIntegralPotentialInverse_fixed k hk₀ hk hδ hκ0 hκ1 V hV H]
  exact ((spectralPotentialIteration_integral_contracting k hk₀ hk hδ hκ0 hκ1 V hV (F + H)).fixedPoint_unique hfixed).symm

theorem spectralIntegralPotentialInverse_smul {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ)
    (c : ℝ) (F : ℝ →ᵇ SpectralSpace ι) :
    spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV (c • F) =
      c • spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F := by
  let u := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F
  have hfixed : Function.IsFixedPt (spectralPotentialIteration k hk₀ hk hδ V (c • F)) (c • u) := by
    change spectralResolventCLM k hk₀ hk hδ ((c • F) - V • (c • u)) = c • u
    have heq : (c • F) - V • (c • u) = c • (F - V • u) := by
      apply BoundedContinuousFunction.ext
      intro t
      change c • F t - V t • (c • u t) = c • (F t - V t • u t)
      rw [smul_sub, smul_comm (V t) c]
    rw [heq, map_smul, spectralIntegralPotentialInverse_fixed k hk₀ hk hδ hκ0 hκ1 V hV F]
  exact ((spectralPotentialIteration_integral_contracting k hk₀ hk hδ hκ0 hκ1 V hV (c • F)).fixedPoint_unique hfixed).symm

def spectralIntegralPotentialInverseCLM {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ) :
    (ℝ →ᵇ SpectralSpace ι) →L[ℝ] (ℝ →ᵇ SpectralSpace ι) :=
  ({ toFun := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV
     map_add' := spectralIntegralPotentialInverse_add k hk₀ hk hδ hκ0 hκ1 V hV
     map_smul' := spectralIntegralPotentialInverse_smul k hk₀ hk hδ hκ0 hκ1 V hV } :
    (ℝ →ᵇ SpectralSpace ι) →ₗ[ℝ] (ℝ →ᵇ SpectralSpace ι)).mkContinuous
      ((k₀ ^ 2 - δ ^ 2)⁻¹ * (1 - κ)⁻¹) (fun F => by
        change ‖spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F‖ ≤ _
        convert spectralIntegralPotentialInverse_norm_le k hk₀ hk hδ hκ0 hκ1 V hV F using 1 <;>
          simp only [div_eq_mul_inv] <;> ring)

theorem spectralIntegralPotentialInverseCLM_norm_le {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ) :
    ‖spectralIntegralPotentialInverseCLM k hk₀ hk hδ hκ0 hκ1 V hV‖ ≤
      (k₀ ^ 2 - δ ^ 2)⁻¹ * (1 - κ)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (inv_nonneg.mpr (spectral_gap_positive hk₀ hδ).le)
      (inv_nonneg.mpr (sub_pos.mpr hκ1).le))
  intro F
  change ‖spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F‖ ≤ _
  convert spectralIntegralPotentialInverse_norm_le k hk₀ hk hδ hκ0 hκ1 V hV F using 1 <;>
    simp only [div_eq_mul_inv] <;> ring

end Yamabe3.Analysis.Delaunay
