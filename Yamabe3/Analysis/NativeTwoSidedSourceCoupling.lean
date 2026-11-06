import Yamabe3.Analysis.NativeExteriorNormalHighSupport
import Yamabe3.Analysis.NativeFullSourceBoundaryCorrection
import Yamabe3.Analysis.NativeBoundaryPoissonOperators

/-! The coupled high inverse is fed the actual difference of the two
inhomogeneous normal traces. Both sources stay independently visible;
the three-halves boundary regularity is proved from their real half-order
trace budgets, not supplied as a new main-theorem assumption. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

abbrev NativeTwoSidedSource := Lp AngularSpectralSpace 2 (volume : Measure ℝ) × Lp AngularSpectralSpace 2 (volume : Measure ℝ)
variable (P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1) (t₀ : ℝ)

def nativeTwoSidedNormalJumpCLM : NativeTwoSidedSource →L[ℝ] AngularL2 :=
  (nativeBubbleExteriorHighNormalCLM t₀).comp (ContinuousLinearMap.snd ℝ _ _)-
    (nativeFullL2NormalAngularCLM P hp v hv hb).comp (ContinuousLinearMap.fst ℝ _ _)

def nativeTwoSidedSourceSigmaCLM : NativeTwoSidedSource →L[ℝ] AngularH1 :=
  (nativeHighCoupledDtNInverse (fullBubbleHighPotential (-t₀)) P).comp
    (nativeTwoSidedNormalJumpCLM P hp v hv hb t₀)

theorem nativeTwoSidedSourceSigma_high (X : NativeTwoSidedSource) :
    nativeHighEnergyProjectionCLM (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X)=
      nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X := nativeHighCoupledDtNInverse_high _ _ _

theorem nativeTwoSidedNormalJump_regular (X : NativeTwoSidedSource) :
    NativeAngularSpectralRegular (1/2) (nativeTwoSidedNormalJumpCLM P hp v hv hb t₀ X) :=
  (nativeAngularSpectralRegular_sub
    (nativeExteriorL2HighNormalAngular_half_bound (fullBubbleHighPotential t₀) (fullBubbleHighPotential (-t₀))
      (fullBubblePhasePotential_plus_kernel t₀) X.2).1
    (nativeFullL2NormalAngular_half_bound P hp v hv hb X.1).1).1

theorem nativeTwoSidedSourceSigma_regular (X : NativeTwoSidedSource) :
    NativeAngularSpectralRegular (3/2) (angularEmbedding (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X)) := by
  have h := (nativeHighCoupled_inverse_spectral_regular (fullBubbleHighPotential (-t₀)) P (1/2)
    (nativeTwoSidedNormalJumpCLM P hp v hv hb t₀ X) (nativeTwoSidedNormalJump_regular P hp v hv hb t₀ X)).1
  convert h using 1 <;> norm_num [nativeTwoSidedSourceSigmaCLM,ContinuousLinearMap.comp_apply]

theorem nativeTwoSidedSourceSigma_equation (X : NativeTwoSidedSource) :
    (fullBubbleHighPotential (-t₀)).dtn (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X)+
      P.dtn (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X)=
      nativeBubbleExteriorHighNormalCLM t₀ X.2-nativeHighProjection (nativeFullL2NormalAngularCLM P hp v hv hb X.1) := by
  change ((fullBubbleHighPotential (-t₀)).dtn+P.dtn)
    (nativeHighCoupledDtNInverse (fullBubbleHighPotential (-t₀)) P (nativeTwoSidedNormalJumpCLM P hp v hv hb t₀ X))=_
  rw [nativeHighCoupledDtNInverse_right]
  change nativeHighProjection (nativeBubbleExteriorHighNormalCLM t₀ X.2-nativeFullL2NormalAngularCLM P hp v hv hb X.1)=_
  rw [map_sub]
  have he : nativeHighProjection (nativeBubbleExteriorHighNormalCLM t₀ X.2)=nativeBubbleExteriorHighNormalCLM t₀ X.2 :=
    nativeExteriorL2HighNormalAngular_high _ _ _ X.2
  rw [he]

theorem exists_nativeTwoSidedSourceSigma_energy :
    ∃D : ℝ,0≤D ∧ ∀X : NativeTwoSidedSource,
      nativePoissonBoundaryEnergy (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X)≤D*‖X‖^2 := by
  let B := fullBubbleHighPotential (-t₀)
  let Q := fullBubbleHighPotential t₀
  let CE := (3+4*B.derivativeBound^2)*(50/9)*(1+‖Q.potential‖*((1-Q.κ)⁻¹*(4/9)))^2
  let CI := 2*(3+4*P.derivativeBound^2)*(50/9)*(1+‖P.potential‖*((1-P.κ)⁻¹*(4/9)))^2+
    7744*(eLpNorm (futureL2Kernel 2) 2).toReal^2
  let T := nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀
  have hCE : 0≤CE := by dsimp [CE];positivity
  have hCI : 0≤CI := by dsimp [CI];positivity
  refine ⟨‖T‖^2+8*(CE+CI),by positivity,fun X => ?_⟩
  have he := nativeExteriorL2HighNormalAngular_half_bound Q B (fullBubblePhasePotential_plus_kernel t₀) X.2
  have hi := nativeFullL2NormalAngular_half_bound P hp v hv hb X.1
  have hj := nativeAngularSpectralRegular_sub he.1 hi.1
  have hs := nativeHighCoupled_inverse_spectral_regular B P (1/2)
    (nativeTwoSidedNormalJumpCLM P hp v hv hb t₀ X) (nativeTwoSidedNormalJump_regular P hp v hv hb t₀ X)
  have hs' : (∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding (T X)) i)≤
      4*(∑'i,nativeAngularWeightedSquare (1/2) (nativeTwoSidedNormalJumpCLM P hp v hv hb t₀ X) i) := by
    convert hs.2 using 1 <;> norm_num [B,T,nativeTwoSidedSourceSigmaCLM,ContinuousLinearMap.comp_apply]
  have hF : ‖X.1‖^2≤‖X‖^2 := by nlinarith [norm_fst_le X,norm_nonneg X.1,norm_nonneg X]
  have hG : ‖X.2‖^2≤‖X‖^2 := by nlinarith [norm_snd_le X,norm_nonneg X.2,norm_nonneg X]
  have hE := mul_le_mul_of_nonneg_left hG hCE
  have hI := mul_le_mul_of_nonneg_left hF hCI
  have ht : ‖T X‖^2≤‖T‖^2*‖X‖^2 := by
    have ht := T.le_opNorm X
    have hn : 0≤‖T‖*‖X‖ := mul_nonneg (norm_nonneg T) (norm_nonneg X)
    nlinarith [norm_nonneg (T X)]
  have he' : (∑'i,nativeAngularWeightedSquare (1/2) (nativeBubbleExteriorHighNormalCLM t₀ X.2) i)≤CE*‖X.2‖^2 := he.2
  have hi' : (∑'i,nativeAngularWeightedSquare (1/2) (nativeFullL2NormalAngularCLM P hp v hv hb X.1) i)≤CI*‖X.1‖^2 := hi.2
  have hj' := hj.2
  change (∑'i,nativeAngularWeightedSquare (1/2) (nativeTwoSidedNormalJumpCLM P hp v hv hb t₀ X) i)≤2*((∑'i,nativeAngularWeightedSquare (1/2) (nativeBubbleExteriorHighNormalCLM t₀ X.2) i)+
    (∑'i,nativeAngularWeightedSquare (1/2) (nativeFullL2NormalAngularCLM P hp v hv hb X.1) i)) at hj' 
  unfold nativePoissonBoundaryEnergy
  change ‖T X‖^2+(∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding (T X)) i)≤_
  nlinarith only [ht,hs',hj',he',hi',hE,hI]

#print axioms nativeTwoSidedSourceSigma_high
#print axioms nativeTwoSidedNormalJump_regular
#print axioms nativeTwoSidedSourceSigma_regular
#print axioms nativeTwoSidedSourceSigma_equation
#print axioms exists_nativeTwoSidedSourceSigma_energy
end Yamabe3.Analysis.SpherePolar
