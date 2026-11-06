import Yamabe3.Analysis.SpectralPotentialNormalBudget
import Yamabe3.Analysis.NativeAngularHalfRegularity
import Yamabe3.Analysis.NativeL2PotentialEntrance

/-! Half-order regularity of the physical normal datum of the original
continuous L2 particular field. The sign and conformal half-weight are
kept literally. Identification with the collar trace is a separate proof. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum
variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
  (hm : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)

def nativeContinuousParticularNormal (F : ℝ →ᵇ SpectralSpace AngularIndex) : AngularL2 :=
  let U := spectralIntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
    (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hm F
  let D := spectralFirstDerivativeConvolution nativeAngularRate (by norm_num) nativeAngularRate_lower (-2) (F-V • U) 0
  nativeHighProjection (-(angularBasis.repr.symm D)-(1/2:ℝ) • angularBasis.repr.symm (U 0))

theorem nativeContinuousParticularNormal_half_bound
    (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|V (t-s)|)≤κ)
    (F : ℝ →ᵇ SpectralSpace AngularIndex) (hF : MemLp F 2) :
    NativeAngularSpectralRegular (1/2) (nativeContinuousParticularNormal hκ0 hκ1 V hm F) ∧
      (∑' i,nativeAngularWeightedSquare (1/2) (nativeContinuousParticularNormal hκ0 hκ1 V hm F) i)≤
        (50/9)*(1+‖V‖*((1-κ)⁻¹*(4/9)))^2*‖hF.toLp F‖^2 := by
  let U := spectralIntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
    (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hm F
  let D := spectralFirstDerivativeConvolution nativeAngularRate (by norm_num) nativeAngularRate_lower (-2) (F-V • U) 0
  obtain ⟨_,hD,hDb⟩ := spectralIntegralPotentialInverse_normal_budget nativeAngularRate
    (by norm_num : (0:ℝ)<5/2) nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2)
    hκ0 hκ1 V hm (by simpa only [neg_neg] using hp) F hF 0
  obtain ⟨hd,hdb⟩ := nativeAngular_synthesis_one_half_bound D hD
  obtain ⟨hu,hub⟩ := nativeL2PotentialEntrance_three_halves hκ0 hκ1 V hm hp (hF.toLp F) 0
  rw [spectralL2PotentialContinuous_agrees_original nativeAngularRate
    (by norm_num) nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2)
    hκ0 hκ1 V hm (by simpa only [neg_neg] using hp) F hF] at hu hub
  obtain ⟨hu',hub'⟩ := nativeAngular_three_halves_to_half (angularBasis.repr.symm (U 0)) hu
  obtain ⟨hdn,hdnb⟩ := nativeAngularSpectralRegular_smul hd (-1)
  obtain ⟨hu2,hu2b⟩ := nativeAngularSpectralRegular_smul hu' (1/2)
  simp only [neg_one_smul] at hdn hdnb
  obtain ⟨hsub,hsubb⟩ := nativeAngularSpectralRegular_sub hdn hu2
  obtain ⟨hr,hrb⟩ := nativeAngularSpectralRegular_high hsub
  refine ⟨hr,hrb.trans ?_⟩
  norm_num at hDb hdnb hu2b
  change (∑' i,nativeAngularRate i*(D i)^2)≤_ at hDb
  change (∑' i,nativeAngularWeightedSquare (3/2) (angularBasis.repr.symm (U 0)) i)≤_ at hub
  simp only [Lp.norm_toLp] at hub ⊢
  nlinarith only [hDb,hdb,hub,hub',hdnb,hu2b,hsubb]

#print axioms nativeContinuousParticularNormal_half_bound
end Yamabe3.Analysis.Delaunay
