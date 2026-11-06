import Mathlib.Analysis.InnerProductSpace.l2Space
import Yamabe3.Analysis.SpectralL2EntranceRegularity
import Yamabe3.Analysis.SpectralL2PotentialContinuous

/-! The actual same-potential continuous representative has a uniform
three-halves spectral entrance budget. The source is the original L2
source; its residual is constructed using the same inverse. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem spectralL2Potential_residual_norm_le {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (hκ0 : 0 ≤ κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s * |V (t-s)|) ≤ κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s * |V (t-s)|) ≤ κ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    ‖F-spectralL2PotentialMulCLM V (spectralL2IntegralPotentialInverse k hk₀ hk hδ V F)‖ ≤
      (1+‖V‖*((1-κ)⁻¹*(1/(k₀^2-δ^2))))*‖F‖ := by
  let U := spectralL2IntegralPotentialInverse k hk₀ hk hδ V F
  let B := (1-κ)⁻¹*(1/(k₀^2-δ^2))
  have hU : ‖U‖ ≤ B*‖F‖ :=
    ((spectralL2IntegralPotentialInverse k hk₀ hk hδ V).le_opNorm F).trans
      (mul_le_mul_of_nonneg_right (spectralL2IntegralPotentialInverse_norm_le k hk₀ hk hδ hκ0 hκ1 V hminus hplus) (norm_nonneg _))
  calc
    _ ≤ ‖F‖+‖spectralL2PotentialMul V U‖ := norm_sub_le _ _
    _ ≤ ‖F‖+‖V‖*(B*‖F‖) := add_le_add_right
      ((spectralL2PotentialMul_norm_le V U).trans (mul_le_mul_of_nonneg_left hU (norm_nonneg _))) _
    _ = _ := by ring

theorem spectralL2PotentialContinuous_entrance_regular {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (hκ0 : 0 ≤ κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s * |V (t-s)|) ≤ κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s * |V (t-s)|) ≤ κ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) (t : ℝ) :
    let U := spectralL2PotentialContinuousCLM k hk₀ hk hδ V F t
    Summable (fun i => k i^3*(U i)^2) ∧
      (∑' i,k i^3*(U i)^2) ≤ (k₀^2/(4*(k₀^2-δ^2)))*
        (1+‖V‖*((1-κ)⁻¹*(1/(k₀^2-δ^2))))^2*‖F‖^2 := by
  let G := F-spectralL2PotentialMulCLM V (spectralL2IntegralPotentialInverse k hk₀ hk hδ V F)
  obtain ⟨hs,hb⟩ := spectralL2Convolution_entrance_spectral_regular k hk₀ hk hδ G (Lp.memLp G) t
  have he : (∫ a : ℝ,‖G a‖^2)=‖G‖^2 := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [he] at hb
  have hg := spectral_gap_positive hk₀ hδ
  have hn := spectralL2Potential_residual_norm_le k hk₀ hk hδ hκ0 hκ1 V hminus hplus F
  have hsq := pow_le_pow_left₀ (norm_nonneg G) hn 2
  refine ⟨hs,hb.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ k₀^2/(4*(k₀^2-δ^2)))
  simpa only [mul_pow,mul_assoc] using hh

#print axioms spectralL2Potential_residual_norm_le
#print axioms spectralL2PotentialContinuous_entrance_regular
end Yamabe3.Analysis.Delaunay
