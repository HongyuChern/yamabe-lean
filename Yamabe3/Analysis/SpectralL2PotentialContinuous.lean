import Yamabe3.Analysis.SpectralL2SmoothingCLM
import Mathlib.MeasureTheory.Measure.OpenPos

/-! A canonical bounded continuous representative and its genuine bounded
entrance value for the same L2 potential inverse. The source and the
potential are unchanged; continuity is constructed by the free integral. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

def spectralL2PotentialContinuousCLM {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (V : ℝ →ᵇ ℝ) :
    Lp (SpectralSpace ι) 2 (volume : Measure ℝ) →L[ℝ] (ℝ →ᵇ SpectralSpace ι) :=
  (spectralL2SmoothingCLM k hk₀ hk hδ).comp
    (ContinuousLinearMap.id ℝ _-(spectralL2PotentialMulCLM V).comp
      (spectralL2IntegralPotentialInverse k hk₀ hk hδ V))

def spectralL2PotentialEntranceCLM {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (V : ℝ →ᵇ ℝ) :
    Lp (SpectralSpace ι) 2 (volume : Measure ℝ) →L[ℝ] SpectralSpace ι :=
  (BoundedContinuousFunction.evalCLM ℝ 0).comp (spectralL2PotentialContinuousCLM k hk₀ hk hδ V)

theorem spectralL2PotentialContinuous_coe_ae {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (hκ0 : 0 ≤ κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s * |V (t-s)|) ≤ κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s * |V (t-s)|) ≤ κ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    (spectralL2PotentialContinuousCLM k hk₀ hk hδ V F : ℝ → SpectralSpace ι)=ᵐ[volume]
      (spectralL2IntegralPotentialInverse k hk₀ hk hδ V F : ℝ → SpectralSpace ι) := by
  let G := F-spectralL2PotentialMulCLM V (spectralL2IntegralPotentialInverse k hk₀ hk hδ V F)
  have h := spectralL2Resolvent_coe_ae k hk₀ hk hδ G
  change (spectralL2FreeCLM k hk₀ hk hδ G : ℝ → SpectralSpace ι)=ᵐ[volume]
    spectralL2Convolution k hk₀ hk δ G at h
  have hf := spectralL2IntegralPotentialInverse_fixed k hk₀ hk hδ hκ0 hκ1 V hminus hplus F
  change spectralL2IntegralPotentialInverse k hk₀ hk hδ V F=spectralL2FreeCLM k hk₀ hk hδ G at hf
  rw [←hf] at h
  exact h.symm

theorem spectralL2PotentialContinuous_agrees_original {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (hκ0 : 0 ≤ κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s * |V (t-s)|) ≤ κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s * |V (t-s)|) ≤ κ)
    (F : ℝ →ᵇ SpectralSpace ι) (hF : MemLp F 2) :
    spectralL2PotentialContinuousCLM k hk₀ hk hδ V (hF.toLp F)=
      spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hminus F := by
  apply BoundedContinuousFunction.ext
  intro t
  have he := Measure.eq_of_ae_eq
    ((spectralL2PotentialContinuous_coe_ae k hk₀ hk hδ hκ0 hκ1 V hminus hplus _).trans
      (spectralL2IntegralPotentialInverse_agrees_original k hk₀ hk hδ hκ0 hκ1 V hminus hplus F hF))
    (spectralL2PotentialContinuousCLM k hk₀ hk hδ V (hF.toLp F)).continuous
    (spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hminus F).continuous
  exact congrFun he t

theorem spectralL2PotentialContinuous_norm_le {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (hκ0 : 0 ≤ κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s * |V (t-s)|) ≤ κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s * |V (t-s)|) ≤ κ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    ‖spectralL2PotentialContinuousCLM k hk₀ hk hδ V F‖ ≤
      (eLpNorm (spectralMajorant k₀ δ) 2).toReal*
        (1+‖V‖*((1-κ)⁻¹*(1/(k₀^2-δ^2))))*‖F‖ := by
  let U := spectralL2IntegralPotentialInverse k hk₀ hk hδ V F
  let B := (1-κ)⁻¹*(1/(k₀^2-δ^2))
  have hU : ‖U‖ ≤ B*‖F‖ :=
    ((spectralL2IntegralPotentialInverse k hk₀ hk hδ V).le_opNorm F).trans
      (mul_le_mul_of_nonneg_right (spectralL2IntegralPotentialInverse_norm_le k hk₀ hk hδ hκ0 hκ1 V hminus hplus) (norm_nonneg _))
  have hM := spectralL2PotentialMul_norm_le V U
  have hG : ‖F-spectralL2PotentialMulCLM V U‖ ≤ (1+‖V‖*B)*‖F‖ := by
    calc
      _ ≤ ‖F‖+‖spectralL2PotentialMul V U‖ := norm_sub_le _ _
      _ ≤ ‖F‖+‖V‖*(B*‖F‖) := add_le_add_right (hM.trans (mul_le_mul_of_nonneg_left hU (norm_nonneg _))) _
      _ = _ := by ring
  exact (spectralL2SmoothCurve_norm_le k hk₀ hk hδ _).trans
    ((mul_le_mul_of_nonneg_left hG ENNReal.toReal_nonneg).trans_eq (by ring))

#print axioms spectralL2PotentialContinuous_coe_ae
#print axioms spectralL2PotentialContinuous_agrees_original
#print axioms spectralL2PotentialContinuous_norm_le
end Yamabe3.Analysis.Delaunay
