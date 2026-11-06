import Yamabe3.Analysis.LowL2Continuous
import Yamabe3.Analysis.SpectralL2OriginalSquareBound

/-! Actual value and scalar-potential residual L2 bounds for the same
low solution. These are bounds of volume integrands, not new source inputs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
variable {ι : Type*}

def lowL2ResidualCLM (A : ℝ →ᵇ (SpectralSpace ι →L[ℝ] SpectralSpace ι)) (hA : ‖A‖ ≤ 7/2)
    (V : ℝ →ᵇ ℝ) : Lp (SpectralSpace ι) 2 (volume : Measure ℝ) →L[ℝ] Lp (SpectralSpace ι) 2 (volume : Measure ℝ) :=
  ContinuousLinearMap.id ℝ _-(spectralL2PotentialMulCLM V).comp (lowL2FutureInverseCLM A hA)

theorem lowL2Residual_norm (A : ℝ →ᵇ (SpectralSpace ι →L[ℝ] SpectralSpace ι)) (hA : ‖A‖ ≤ 7/2)
    (V : ℝ →ᵇ ℝ) (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    ‖lowL2ResidualCLM A hA V F‖ ≤ (1+2*‖V‖)*‖F‖ := by
  have hu := (lowL2FutureInverseCLM A hA).le_of_opNorm_le (lowL2FutureInverse_norm A hA) F
  have hm := spectralL2PotentialMul_norm_le V (lowL2FutureInverseCLM A hA F)
  change ‖F-spectralL2PotentialMulCLM V (lowL2FutureInverseCLM A hA F)‖ ≤ _
  apply (norm_sub_le _ _).trans
  change ‖spectralL2PotentialMulCLM V (lowL2FutureInverseCLM A hA F)‖ ≤
    ‖V‖*‖lowL2FutureInverseCLM A hA F‖ at hm
  have hb := hm.trans (mul_le_mul_of_nonneg_left hu (norm_nonneg V))
  nlinarith

theorem lowL2Residual_ae (A : ℝ →ᵇ (SpectralSpace ι →L[ℝ] SpectralSpace ι)) (hA : ‖A‖ ≤ 7/2)
    (V : ℝ →ᵇ ℝ) (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    (lowL2ResidualCLM A hA V F : ℝ → SpectralSpace ι)=ᵐ[volume]
      (fun t => F t-V t • lowL2ContinuousCLM A hA F t) := by
  let R := lowL2FutureInverseCLM A hA F
  filter_upwards [Lp.coeFn_sub F (spectralL2PotentialMulCLM V R),
    spectralL2PotentialMul_coe_ae V R,lowL2Continuous_ae A hA F] with t hs hm hu
  change (F-spectralL2PotentialMulCLM V R) t=_
  change (spectralL2PotentialMulCLM V R) t=V t • R t at hm
  change lowL2ContinuousCLM A hA F t=R t at hu
  rw [hs]
  change F t-(spectralL2PotentialMulCLM V R) t=_
  rw [hm,←hu]

theorem lowL2Continuous_square_bounds (A : ℝ →ᵇ (SpectralSpace ι →L[ℝ] SpectralSpace ι)) (hA : ‖A‖ ≤ 7/2)
    (V : ℝ →ᵇ ℝ) (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    let U := lowL2ContinuousCLM A hA F
    let G := fun t => F t-V t • U t
    MemLp U 2 ∧ MemLp G 2 ∧
      (∫ t : ℝ,‖U t‖^2) ≤ 4*‖F‖^2 ∧
      (∫ t : ℝ,‖G t‖^2) ≤ (1+2*‖V‖)^2*‖F‖^2 := by
  let R := lowL2FutureInverseCLM A hA F
  let U := lowL2ContinuousCLM A hA F
  let G := fun t => F t-V t • U t
  let H := lowL2ResidualCLM A hA V F
  have hu : (R : ℝ → SpectralSpace ι)=ᵐ[volume]U := (lowL2Continuous_ae A hA F).symm
  have hg : (H : ℝ → SpectralSpace ι)=ᵐ[volume]G := lowL2Residual_ae A hA V F
  refine ⟨(Lp.memLp R).ae_eq hu,(Lp.memLp H).ae_eq hg,?_,?_⟩
  · rw [spectralL2_norm_square_of_ae R U hu]
    have hn := (lowL2FutureInverseCLM A hA).le_of_opNorm_le (lowL2FutureInverse_norm A hA) F
    simpa only [mul_pow,show (2:ℝ)^2=4 by norm_num] using pow_le_pow_left₀ (norm_nonneg R) hn 2
  · rw [spectralL2_norm_square_of_ae H G hg]
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg H) (lowL2Residual_norm A hA V F) 2

#print axioms lowL2Residual_norm
#print axioms lowL2Residual_ae
#print axioms lowL2Continuous_square_bounds
end Yamabe3.Analysis.Delaunay
