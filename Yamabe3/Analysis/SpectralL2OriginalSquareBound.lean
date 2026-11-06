import Yamabe3.Analysis.SpectralL2PotentialEntranceRegularity

/-! Square-integral bounds of the actual continuous-source solution and
its actual residual, identified with the previously constructed L2 classes. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem spectralL2_norm_square_of_ae {ι : Type*}
    (Z : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) (H : ℝ → SpectralSpace ι)
    (h : (Z : ℝ → SpectralSpace ι)=ᵐ[volume] H) :
    (∫ t : ℝ,‖H t‖^2)=‖Z‖^2 := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h] with t ht
  rw [ht,real_inner_self_eq_norm_sq]

theorem spectralIntegralPotentialInverse_actual_square_bounds {ι : Type*}
    (k : ι → ℝ) {k₀ δ κ : ℝ} (hk₀ : 0<k₀) (hk : ∀ i,k₀≤k i)
    (hδ : |δ|<k₀) (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s*|V (t-s)|)≤κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s*|V (t-s)|)≤κ)
    (F : ℝ →ᵇ SpectralSpace ι) (hF : MemLp F 2) :
    let U := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hminus F
    let G := fun t => F t-V t • U t
    let B := (1-κ)⁻¹*(1/(k₀^2-δ^2))
    MemLp U 2 ∧ MemLp G 2 ∧
      (∫ t : ℝ,‖U t‖^2)≤B^2*‖hF.toLp F‖^2 ∧
      (∫ t : ℝ,‖G t‖^2)≤(1+‖V‖*B)^2*‖hF.toLp F‖^2 := by
  let Z := spectralL2IntegralPotentialInverse k hk₀ hk hδ V (hF.toLp F)
  let U := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hminus F
  let G := fun t => F t-V t • U t
  let H := hF.toLp F-spectralL2PotentialMulCLM V Z
  have hz : (Z : ℝ → SpectralSpace ι)=ᵐ[volume] U :=
    spectralL2IntegralPotentialInverse_agrees_original k hk₀ hk hδ hκ0 hκ1 V hminus hplus F hF
  have hh : (H : ℝ → SpectralSpace ι)=ᵐ[volume] G := by
    filter_upwards [Lp.coeFn_sub (hF.toLp F) (spectralL2PotentialMulCLM V Z),
      hF.coeFn_toLp,spectralL2PotentialMul_coe_ae V Z,hz] with t hs hf hm hu
    change H t=F t-V t • U t
    change (spectralL2PotentialMulCLM V Z) t=V t • Z t at hm
    calc
      H t=(hF.toLp F) t-(spectralL2PotentialMulCLM V Z) t := hs
      _=F t-V t • U t := by rw [hf,hm,hu]
  have hzn := ((spectralL2IntegralPotentialInverse k hk₀ hk hδ V).le_opNorm (hF.toLp F)).trans
    (mul_le_mul_of_nonneg_right
      (spectralL2IntegralPotentialInverse_norm_le k hk₀ hk hδ hκ0 hκ1 V hminus hplus) (norm_nonneg _))
  have hhn := spectralL2Potential_residual_norm_le k hk₀ hk hδ hκ0 hκ1 V hminus hplus (hF.toLp F)
  refine ⟨(Lp.memLp Z).ae_eq hz,(Lp.memLp H).ae_eq hh,?_,?_⟩
  · rw [spectralL2_norm_square_of_ae Z U hz]
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg Z) hzn 2
  · rw [spectralL2_norm_square_of_ae H G hh]
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg H) hhn 2

#print axioms spectralL2_norm_square_of_ae
#print axioms spectralIntegralPotentialInverse_actual_square_bounds
end Yamabe3.Analysis.Delaunay
