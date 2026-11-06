import Yamabe3.Analysis.NativeSupportedOuterNativeEquation
import Yamabe3.Analysis.NativeMatchedJetEquations

/-! The actual finite compensation coefficients are bounded linear
outputs of the retained Cauchy/source data. The Wronskian denominator and
all signs are the original ones. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay

def nativeBubbleCompensationCoefficientCLM (τ : ℝ) (i : AngularIndex) :
    (AngularL2 × AngularL2) →L[ℝ] ℝ :=
  (bubbleCompensationMass i)⁻¹ •
    ((-bubbleLowJacobi i τ) • ((innerSL ℝ (angularBasis i)).comp (ContinuousLinearMap.snd ℝ _ _))+
      deriv (bubbleLowJacobi i) τ • ((innerSL ℝ (angularBasis i)).comp (ContinuousLinearMap.fst ℝ _ _)))

theorem nativeBubbleCompensationCoefficientCLM_apply (τ : ℝ) (i : AngularIndex) (d n : AngularL2) :
    nativeBubbleCompensationCoefficientCLM τ i (d,n)=
      bubbleLowCauchyCompensation i τ (inner ℝ (angularBasis i) d) (inner ℝ (angularBasis i) n) 0 := by
  change (bubbleCompensationMass i)⁻¹*((-bubbleLowJacobi i τ)*inner ℝ (angularBasis i) n+
    deriv (bubbleLowJacobi i) τ*inner ℝ (angularBasis i) d)=_
  unfold bubbleLowCauchyCompensation
  ring

def nativeCauchyCompensationCoefficientCLM (τ : ℝ) (i : AngularIndex) :
    (AngularL2 × AngularL2) →L[ℝ] ℝ :=
  (nativeBubbleCompensationCoefficientCLM τ i).comp
    ((ContinuousLinearMap.fst ℝ AngularL2 AngularL2).prod
      (-(ContinuousLinearMap.snd ℝ AngularL2 AngularL2)-(1/2:ℝ) • (ContinuousLinearMap.fst ℝ _ _)))

theorem nativeCauchyCompensationCoefficientCLM_apply {τ : ℝ} (ht : 0<τ)
    (i : AngularIndex) (D N : AngularL2) :
    nativeCauchyCompensationCoefficientCLM τ i (D,N)=nativeCauchyCompensationData ht D N i := by
  change nativeBubbleCompensationCoefficientCLM τ i (D,-N-(1/2:ℝ) • D)=_
  exact nativeBubbleCompensationCoefficientCLM_apply τ i _ _

def nativeSupportedCompensationCoefficientCLM (P : NativeHighPotential)
    (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
    (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)
    (b τ : ℝ) (i : AngularIndex) : NativeTwoSidedSource →L[ℝ] ℝ :=
  (nativeBubbleCompensationCoefficientCLM τ i).comp
    ((nativeBubbleLowCorrectionDataCLM τ).comp
      ((nativeSupportedLowPhysicalDataCLM b).comp (nativeTwoSidedExteriorDataCLM P hp v hv hb)))

theorem nativeSupportedCompensationCoefficientCLM_apply (P : NativeHighPotential)
    (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
    (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)
    (b : ℝ) {τ : ℝ} (ht : 0<τ) (i : AngularIndex) (X : NativeTwoSidedSource) :
    nativeSupportedCompensationCoefficientCLM P hp v hv hb b τ i X=
      nativeSupportedTwoSidedExteriorCompensation P hp v hv hb b ht X i := by
  exact nativeBubbleCompensationCoefficientCLM_apply τ i _ _

theorem exists_finite_coefficientCLM_bound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {ι : Type*} (s : Finset ι) (L : ι → H →L[ℝ] ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀x : H,∀i∈s,‖L i x‖≤C*‖x‖ := by
  refine ⟨∑i∈s,‖L i‖,Finset.sum_nonneg (fun i _ => norm_nonneg _),?_⟩
  intro x i hi
  exact ((L i).le_opNorm x).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => norm_nonneg (L j)) hi) (norm_nonneg x))

#print axioms nativeBubbleCompensationCoefficientCLM_apply
#print axioms nativeCauchyCompensationCoefficientCLM_apply
#print axioms nativeSupportedCompensationCoefficientCLM_apply
#print axioms exists_finite_coefficientCLM_bound
end Yamabe3.Analysis.SpherePolar
