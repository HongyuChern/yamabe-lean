import Yamabe3.Analysis.SpectralConvolution
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Actual bounded Hilbert-space inverse with a common scalar potential

The contraction acts on C_b(R, lp 2) itself, using the diagonal operator
kernel norm. Every spectral mode is solved by the same fixed point. In
particular this proof never sums individual time-supremum bounds.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

def spectralPotentialIteration {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (V : ℝ →ᵇ ℝ) (F u : ℝ →ᵇ SpectralSpace ι) : ℝ →ᵇ SpectralSpace ι :=
  spectralResolventCLM k hk₀ hk hδ (F - V • u)

theorem spectralPotentialIteration_contracting {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (V : ℝ →ᵇ ℝ) (F : ℝ →ᵇ SpectralSpace ι)
    (hV : ‖V‖ < k₀ ^ 2 - δ ^ 2) :
    ContractingWith ⟨‖V‖ / (k₀ ^ 2 - δ ^ 2),
      div_nonneg (norm_nonneg _) (spectral_gap_positive hk₀ hδ).le⟩
      (spectralPotentialIteration k hk₀ hk hδ V F) := by
  have hgap := spectral_gap_positive hk₀ hδ
  refine ⟨(div_lt_one hgap).mpr hV, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro u w
  rw [dist_eq_norm, dist_eq_norm]
  change ‖spectralResolventCLM k hk₀ hk hδ (F - V • u) -
    spectralResolventCLM k hk₀ hk hδ (F - V • w)‖ ≤
      (‖V‖ / (k₀ ^ 2 - δ ^ 2)) * ‖u - w‖
  rw [← map_sub]
  have heq : (F - V • u) - (F - V • w) = -(V • (u - w)) := by
    apply BoundedContinuousFunction.ext
    intro t
    change F t - V t • u t - (F t - V t • w t) = -(V t • (u t - w t))
    rw [smul_sub]
    abel
  rw [heq, map_neg, norm_neg]
  calc
    _ ≤ ‖V • (u - w)‖ / (k₀ ^ 2 - δ ^ 2) := spectralResolvent_norm_le k hk₀ hk hδ _
    _ ≤ (‖V‖ * ‖u - w‖) / (k₀ ^ 2 - δ ^ 2) :=
      div_le_div_of_nonneg_right (norm_smul_le _ _) hgap.le
    _ = _ := by ring

/-- The actual fixed point in the complete space of Hilbert-valued bounded
continuous functions. The input is a small potential, never an inverse. -/
def spectralPotentialInverse {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (V : ℝ →ᵇ ℝ) (hV : ‖V‖ < k₀ ^ 2 - δ ^ 2)
    (F : ℝ →ᵇ SpectralSpace ι) : ℝ →ᵇ SpectralSpace ι :=
  (spectralPotentialIteration_contracting k hk₀ hk hδ V F hV).fixedPoint
    (spectralPotentialIteration k hk₀ hk hδ V F)

theorem spectralPotentialInverse_fixed {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (V : ℝ →ᵇ ℝ) (hV : ‖V‖ < k₀ ^ 2 - δ ^ 2)
    (F : ℝ →ᵇ SpectralSpace ι) :
    spectralResolventCLM k hk₀ hk hδ (F - V • spectralPotentialInverse k hk₀ hk hδ V hV F) =
      spectralPotentialInverse k hk₀ hk hδ V hV F :=
  (spectralPotentialIteration_contracting k hk₀ hk hδ V F hV).fixedPoint_isFixedPt

theorem spectralPotentialInverse_norm_le {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (V : ℝ →ᵇ ℝ) (hV : ‖V‖ < k₀ ^ 2 - δ ^ 2)
    (F : ℝ →ᵇ SpectralSpace ι) :
    ‖spectralPotentialInverse k hk₀ hk hδ V hV F‖ ≤
      ‖F‖ / (k₀ ^ 2 - δ ^ 2 - ‖V‖) := by
  let u := spectralPotentialInverse k hk₀ hk hδ V hV F
  have heq := spectralPotentialInverse_fixed k hk₀ hk hδ V hV F
  have hgap := spectral_gap_positive hk₀ hδ
  have hn : ‖u‖ ≤ (‖F‖ + ‖V‖ * ‖u‖) / (k₀ ^ 2 - δ ^ 2) := by
    calc
      ‖u‖ = ‖spectralResolventCLM k hk₀ hk hδ (F - V • u)‖ := congrArg norm heq.symm
      _ ≤ ‖F - V • u‖ / (k₀ ^ 2 - δ ^ 2) := spectralResolvent_norm_le k hk₀ hk hδ _
      _ ≤ (‖F‖ + ‖V‖ * ‖u‖) / (k₀ ^ 2 - δ ^ 2) :=
        div_le_div_of_nonneg_right
          ((norm_sub_le _ _).trans (add_le_add le_rfl (norm_smul_le V u))) hgap.le
  have hmul := (le_div_iff₀ hgap).mp hn
  apply (le_div_iff₀ (sub_pos.mpr hV)).mpr
  dsimp only [u] at hmul ⊢
  nlinarith

theorem spectralPotentialInverse_add {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (V : ℝ →ᵇ ℝ) (hV : ‖V‖ < k₀ ^ 2 - δ ^ 2)
    (F H : ℝ →ᵇ SpectralSpace ι) :
    spectralPotentialInverse k hk₀ hk hδ V hV (F + H) =
      spectralPotentialInverse k hk₀ hk hδ V hV F + spectralPotentialInverse k hk₀ hk hδ V hV H := by
  let u := spectralPotentialInverse k hk₀ hk hδ V hV F
  let w := spectralPotentialInverse k hk₀ hk hδ V hV H
  have hfixed : Function.IsFixedPt (spectralPotentialIteration k hk₀ hk hδ V (F + H)) (u + w) := by
    change spectralResolventCLM k hk₀ hk hδ ((F + H) - V • (u + w)) = u + w
    have heq : (F + H) - V • (u + w) = (F - V • u) + (H - V • w) := by
      apply BoundedContinuousFunction.ext
      intro t
      change F t + H t - V t • (u t + w t) = (F t - V t • u t) + (H t - V t • w t)
      rw [smul_add]
      abel
    rw [heq, map_add, spectralPotentialInverse_fixed k hk₀ hk hδ V hV F,
      spectralPotentialInverse_fixed k hk₀ hk hδ V hV H]
  exact ((spectralPotentialIteration_contracting k hk₀ hk hδ V (F + H) hV).fixedPoint_unique hfixed).symm

end Yamabe3.Analysis.Delaunay
