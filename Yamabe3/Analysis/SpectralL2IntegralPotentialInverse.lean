import Yamabe3.Analysis.SpectralL2NeumannBound
import Mathlib.Analysis.SpecificLimits.Normed

/-! An actual operator-norm convergent potential inverse on L2.
This is the whole-line integral fixed point for the original free kernel
and potential, without asserting a half-line entrance condition. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem spectralL2NeumannTerm_summable {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (hκ0 : 0 ≤ κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s * |V (t-s)|) ≤ κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s * |V (t-s)|) ≤ κ) :
    Summable (spectralL2NeumannTerm k hk₀ hk hδ V) := by
  exact ((summable_geometric_of_lt_one hκ0 hκ1).mul_right (1/(k₀^2-δ^2))).of_norm_bounded
    (spectralL2NeumannTerm_norm_le k hk₀ hk hδ hκ0 V hminus hplus)

def spectralL2IntegralPotentialInverse {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (V : ℝ →ᵇ ℝ) :
    Lp (SpectralSpace ι) 2 (volume : Measure ℝ) →L[ℝ] Lp (SpectralSpace ι) 2 (volume : Measure ℝ) :=
  ∑' n,spectralL2NeumannTerm k hk₀ hk hδ V n

theorem spectralL2IntegralPotentialInverse_norm_le {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (hκ0 : 0 ≤ κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s * |V (t-s)|) ≤ κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s * |V (t-s)|) ≤ κ) :
    ‖spectralL2IntegralPotentialInverse k hk₀ hk hδ V‖ ≤ (1-κ)⁻¹*(1/(k₀^2-δ^2)) := by
  have h := tsum_of_norm_bounded (((summable_geometric_of_lt_one hκ0 hκ1).hasSum).mul_right (1/(k₀^2-δ^2)))
    (spectralL2NeumannTerm_norm_le k hk₀ hk hδ hκ0 V hminus hplus)
  rw [tsum_geometric_of_lt_one hκ0 hκ1] at h
  exact h

theorem spectralL2IntegralPotentialInverse_fixed {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (hκ0 : 0 ≤ κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s * |V (t-s)|) ≤ κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s * |V (t-s)|) ≤ κ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    spectralL2IntegralPotentialInverse k hk₀ hk hδ V F =
      spectralL2FreeCLM k hk₀ hk hδ
        (F-spectralL2PotentialMulCLM V (spectralL2IntegralPotentialInverse k hk₀ hk hδ V F)) := by
  let R := spectralL2FreeCLM k hk₀ hk hδ
  let M := spectralL2PotentialMulCLM (ι := ι) V
  let T := spectralL2NeumannTerm k hk₀ hk hδ V
  have hs := spectralL2NeumannTerm_summable k hk₀ hk hδ hκ0 hκ1 V hminus hplus
  let ev := ContinuousLinearMap.apply ℝ (Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) F
  have hsF : Summable (fun n => T n F) := ev.summable hs
  have hsum : spectralL2IntegralPotentialInverse k hk₀ hk hδ V F=∑' n,T n F := ev.map_tsum hs
  have htail : (∑' n,T (n+1) F)= -R (M (spectralL2IntegralPotentialInverse k hk₀ hk hδ V F)) := by
    change (∑' n,-R (M (T n F)))=_
    rw [tsum_neg,← R.map_tsum (M.summable hsF),← M.map_tsum hsF,← hsum]
  calc
    _ = T 0 F+∑' n,T (n+1) F := hsum.trans hsF.tsum_eq_zero_add
    _ = R F-R (M (spectralL2IntegralPotentialInverse k hk₀ hk hδ V F)) := by rw [htail]; rfl
    _ = _ := (map_sub R _ _).symm

#print axioms spectralL2NeumannTerm_summable
#print axioms spectralL2IntegralPotentialInverse_norm_le
#print axioms spectralL2IntegralPotentialInverse_fixed
end Yamabe3.Analysis.Delaunay
