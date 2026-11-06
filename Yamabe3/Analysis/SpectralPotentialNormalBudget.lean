import Yamabe3.Analysis.SpectralL2NormalEntrance
import Yamabe3.Analysis.SpectralL2OriginalSquareBound
import Yamabe3.Analysis.SpectralIntegralWeightedCauchy

/-! The normal derivative budget belongs to the very same potential
fixed point, with the original L2 source on its right hand side. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem spectralIntegralPotentialInverse_normal_budget {ι : Type*}
    (k : ι → ℝ) {k₀ δ κ : ℝ} (hk₀ : 0<k₀) (hk : ∀ i,k₀≤k i)
    (hδ : |δ|<k₀) (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s*|V (t-s)|)≤κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s*|V (t-s)|)≤κ)
    (F : ℝ →ᵇ SpectralSpace ι) (hF : MemLp F 2) (t : ℝ) :
    let U := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hminus F
    let D := spectralFirstDerivativeConvolution k hk₀ hk δ (F-V • U) t
    HasDerivAt (fun s => Real.exp (δ*s) • U s) (Real.exp (δ*t) • D) t ∧
    Summable (fun i => k i*(D i)^2) ∧
      (∑' i,k i*(D i)^2)≤(k₀^2/(4*(k₀^2-δ^2)))*
        (1+‖V‖*((1-κ)⁻¹*(1/(k₀^2-δ^2))))^2*‖hF.toLp F‖^2 := by
  let U := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hminus F
  let G := F-V • U
  obtain ⟨hU,hG,hUb,hGb⟩ := spectralIntegralPotentialInverse_actual_square_bounds
    k hk₀ hk hδ hκ0 hκ1 V hminus hplus F hF
  have hG' : MemLp G 2 := hG
  obtain ⟨hs,hb⟩ := spectralFirstDerivativeConvolution_entrance_spectral_regular k hk₀ hk hδ G hG' t
  refine ⟨spectralIntegralPotentialInverse_weighted_hasDerivAt k hk₀ hk hδ hκ0 hκ1 V hminus F t,hs,?_⟩
  have hg := spectral_gap_positive hk₀ hδ
  have hh := mul_le_mul_of_nonneg_left hGb (by positivity : 0≤k₀^2/(4*(k₀^2-δ^2)))
  exact hb.trans (hh.trans_eq (by ring))

#print axioms spectralIntegralPotentialInverse_normal_budget
end Yamabe3.Analysis.Delaunay
