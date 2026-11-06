import Yamabe3.Analysis.NativeL2CollarLift
import Yamabe3.Analysis.NativeL2ParticularFiniteEquation
import Yamabe3.Analysis.SpectralL2PotentialContinuous

/-! The actual physical high source and the same-potential residual of
an L2 spectral source. The Laplacian residual is F - V U; multiplication
by -8 is kept separate for the physical operator normalization. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeL2HighAngularCLM :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] Lp AngularL2 2 (volume : Measure ℝ) :=
  (nativeHighProjection.comp angularBasis.repr.symm.toLinearIsometry.toContinuousLinearMap).compLpL 2 volume

def nativeL2HighPhysicalSourceCLM :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeL2CollarLiftCLM.comp nativeL2HighAngularCLM

def nativeL2ResidualCLM (V : ℝ →ᵇ ℝ) :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) :=
  ContinuousLinearMap.id ℝ _-(spectralL2PotentialMulCLM V).comp
    (spectralL2IntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
      (by norm_num : |(-2:ℝ)|<5/2) V)

theorem nativeL2HighAngularCLM_ae (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    (nativeL2HighAngularCLM F : ℝ → AngularL2)=ᵐ[volume]
      (fun t => nativeHighProjection (angularBasis.repr.symm (F t))) :=
  (nativeHighProjection.comp angularBasis.repr.symm.toLinearIsometry.toContinuousLinearMap).coeFn_compLpL F

theorem nativeL2HighPhysicalSourceCLM_eq_lift
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ))
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ᵐ t : ℝ ∂volume,(fun θ => w (t,θ))=ᵐ[angularVolume]
      (nativeHighProjection (angularBasis.repr.symm (F t)) : S → ℝ)) :
    (nativeL2HighPhysicalSourceCLM F : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w := by
  apply nativeL2CollarLift_eq_lift _ hw
  filter_upwards [hae,nativeL2HighAngularCLM_ae F] with t ht hF
  change (fun θ => w (t,θ))=ᵐ[angularVolume] (nativeL2HighAngularCLM F t : S → ℝ)
  rw [hF]
  exact ht

theorem nativeL2ResidualCLM_agrees_continuous {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|V (t-s)|)≤κ)
    (F : ℝ →ᵇ SpectralSpace AngularIndex) (hF : MemLp F 2) :
    (nativeL2ResidualCLM V (hF.toLp F) : ℝ → SpectralSpace AngularIndex)=ᵐ[volume]
      (fun t => F t-V t • spectralIntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
        (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hminus F t) := by
  let Z := spectralL2IntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
    (by norm_num : |(-2:ℝ)|<5/2) V (hF.toLp F)
  have hz := spectralL2IntegralPotentialInverse_agrees_original nativeAngularRate
    (by norm_num : (0:ℝ)<5/2) nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2)
    hκ0 hκ1 V hminus (by simpa only [neg_neg] using hplus) F hF
  filter_upwards [Lp.coeFn_sub (hF.toLp F) (spectralL2PotentialMulCLM V Z),
    hF.coeFn_toLp,spectralL2PotentialMul_coe_ae V Z,hz] with t hs hf hm hu
  change (spectralL2PotentialMulCLM V Z) t=V t • Z t at hm
  change Z t=_ at hu
  change (hF.toLp F-spectralL2PotentialMulCLM V Z) t=_
  calc
    _=(hF.toLp F) t-(spectralL2PotentialMulCLM V Z) t := hs
    _=_ := by rw [hf,hm,hu]

#print axioms nativeL2HighAngularCLM_ae
#print axioms nativeL2HighPhysicalSourceCLM_eq_lift
#print axioms nativeL2ResidualCLM_agrees_continuous
end Yamabe3.Analysis.SpherePolar
