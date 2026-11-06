import Yamabe3.Analysis.NativeL2ParticularExtension
import Yamabe3.Analysis.NativeL2ParticularIdentity
import Yamabe3.Analysis.NativeConjugatedCollarLift
import Yamabe3.Analysis.SpectralL2PotentialContinuous
import Yamabe3.Analysis.NativeAngularInverseLinearity

/-! The actual all-L2 H2 collar extension is the physical lift of the
same canonical continuous potential solution, with the high projection
explicitly retained. Equality is transported from the actual dense source
space through two continuous operators, not inferred from similar names. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

def nativeL2ParticularAngularCLM (V : ℝ →ᵇ ℝ) :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] (ℝ →ᵇ AngularL2) :=
  (nativeHighProjection.compLeftContinuousBounded ℝ).comp (angularSynthesisCLM.comp
    (spectralL2PotentialContinuousCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
      (by norm_num : |(-2:ℝ)|<5/2) V))

variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
  (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|V (t-s)|)≤κ)

include hplus in
theorem nativeL2ParticularAngular_agrees_continuous (F : continuousL2Source (SpectralSpace AngularIndex)) :
    nativeConjugatedCurve (nativeL2ParticularAngularCLM V (continuousL2SourceInclusion _ F))=
      nativeL2ParticularCurve hκ0 hκ1 V hminus F.val := by
  have ha := spectralL2PotentialContinuous_agrees_original nativeAngularRate
    (by norm_num : (0:ℝ)<5/2) nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2)
    hκ0 hκ1 V hminus (by simpa using hplus) F.val F.property
  funext t
  change Real.exp (-2*t) • nativeHighProjection (angularBasis.repr.symm
    (spectralL2PotentialContinuousCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
      (by norm_num : |(-2:ℝ)|<5/2) V (F.property.toLp F.val) t))=_
  rw [ha]
  rfl

theorem nativeL2ParticularValueCLM_eq_physical :
    nativeL2ParticularValueCLM hκ0 hκ1 V hminus hplus=
      nativeConjugatedCollarCLM.comp (nativeL2ParticularAngularCLM V) := by
  apply ContinuousLinearMap.ext
  intro F
  have hc := isClosed_eq (nativeL2ParticularValueCLM hκ0 hκ1 V hminus hplus).continuous
    (nativeConjugatedCollarCLM.comp (nativeL2ParticularAngularCLM V)).continuous
  refine (continuousL2SourceInclusion_dense (SpectralSpace AngularIndex)).induction_on F hc ?_
  intro H
  change nativeL2ParticularValueCLM hκ0 hκ1 V hminus hplus (continuousL2SourceInclusion _ H)=_
  rw [(nativeL2ParticularCLM_agrees_continuous hκ0 hκ1 V hminus hplus H).1]
  let W := nativeL2ParticularAngularCLM V (continuousL2SourceInclusion _ H)
  let w := nativeConjugatedJoint W
  have hw := nativeConjugatedJoint_measurable W
  have hae : ∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume] (nativeL2ParticularCurve hκ0 hκ1 V hminus H.val t : S → ℝ) := by
    intro t
    have h := nativeConjugatedJoint_ae W t
    rw [nativeL2ParticularAngular_agrees_continuous hκ0 hκ1 V hminus hplus H] at h
    exact h
  apply Lp.ext
  exact (nativeL2ParticularCollarValue_eq_lift hκ0 hκ1 V hminus hplus H.val H.property hw hae).trans
    (nativeConjugatedCollarLp_eq_lift W hw (nativeConjugatedJoint_ae W)).symm

theorem nativeL2ParticularValueCLM_eq_lift
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ))
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume]
      (nativeConjugatedCurve (nativeL2ParticularAngularCLM V F) t : S → ℝ)) :
    (nativeL2ParticularValueCLM hκ0 hκ1 V hminus hplus F : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      cylinderLift w := by
  rw [nativeL2ParticularValueCLM_eq_physical hκ0 hκ1 V hminus hplus]
  exact nativeConjugatedCollarLp_eq_lift _ hw hae

theorem exists_nativeL2Particular_all_source_same_field_H2
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    ∃ w : ℝ × S → ℝ,Measurable w ∧
      (∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume]
        (nativeConjugatedCurve (nativeL2ParticularAngularCLM V F) t : S → ℝ)) ∧
      (nativeL2ParticularValueCLM hκ0 hκ1 V hminus hplus F : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        cylinderLift w ∧
      MemWkp 2 2 (nativeL2ParticularValueCLM hκ0 hκ1 V hminus hplus F) nativePoissonEntranceCollar ∧
      (∀ j,HasWeakPartialDeriv j (nativeL2ParticularFirstCLM hκ0 hκ1 V hminus hplus j F)
        (nativeL2ParticularValueCLM hκ0 hκ1 V hminus hplus F) nativePoissonEntranceCollar) ∧
      (∀ k j,HasWeakPartialDeriv k (nativeL2ParticularSecondCLM hκ0 hκ1 V hminus hplus k j F)
        (nativeL2ParticularFirstCLM hκ0 hκ1 V hminus hplus j F) nativePoissonEntranceCollar) := by
  let W := nativeL2ParticularAngularCLM V F
  let w := nativeConjugatedJoint W
  have hw := nativeConjugatedJoint_measurable W
  have hae := nativeConjugatedJoint_ae W
  exact ⟨w,hw,hae,nativeL2ParticularValueCLM_eq_lift hκ0 hκ1 V hminus hplus F hw hae,
    nativeL2ParticularCLM_memH2 hκ0 hκ1 V hminus hplus F,
    nativeL2ParticularCLM_weak_jets hκ0 hκ1 V hminus hplus F⟩

#print axioms nativeL2ParticularAngular_agrees_continuous
#print axioms nativeL2ParticularValueCLM_eq_physical
#print axioms nativeL2ParticularValueCLM_eq_lift
#print axioms exists_nativeL2Particular_all_source_same_field_H2
end Yamabe3.Analysis.SpherePolar
