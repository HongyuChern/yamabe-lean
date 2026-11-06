import Yamabe3.Analysis.NativeL2UniformCollarBound
import Yamabe3.Analysis.NativeL2ParticularAllSourceIdentity
import Yamabe3.Analysis.SpectralL2ContinuousTranslation
import Yamabe3.Analysis.NativeWeightedLift

/-! A single all-L2 solution and one measurable representative determine
all scaled physical collars. No new field is selected for each scale. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
  (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|V (t-s)|)≤κ)

include hκ0 hκ1 hminus hplus in
 theorem nativeL2ParticularAngular_translate (s : ℝ)
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeL2ParticularAngularCLM (boundedTimeTranslate ℝ s V)
      (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F)=
        boundedTimeTranslate AngularL2 s (nativeL2ParticularAngularCLM V F) := by
  apply BoundedContinuousFunction.ext
  intro t
  have h := spectralL2PotentialContinuous_translate nativeAngularRate
    (by norm_num : (0:ℝ)<5/2) nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2)
    hκ0 hκ1 V hminus (by simpa using hplus) s F
  change nativeHighProjection (angularBasis.repr.symm
    (spectralL2PotentialContinuousCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
      (by norm_num : |(-2:ℝ)|<5/2) (boundedTimeTranslate ℝ s V)
      (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F) t))=_
  rw [h]
  rfl

 theorem nativeConjugatedCurve_translate (W : ℝ →ᵇ AngularL2) (s t : ℝ) :
    nativeConjugatedCurve (boundedTimeTranslate AngularL2 s W) t=
      Real.exp (2*s) • nativeConjugatedCurve W (t+s) := by
  change Real.exp (-2*t) • W (t+s)=Real.exp (2*s) • (Real.exp (-2*(t+s)) • W (t+s))
  rw [smul_smul,←Real.exp_add]
  congr 2
  ring

 theorem nativeL2ShiftedCollar_same_physical_function
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    ∃ w : ℝ × S → ℝ,Measurable w ∧
      (∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume]
        (nativeConjugatedCurve (nativeL2ParticularAngularCLM V F) t : S → ℝ)) ∧
      ∀ s : ℝ,
        let Vs := boundedTimeTranslate ℝ s V
        let Fs := l2TimeTranslateCLM (SpectralSpace AngularIndex) s F
        let vs := nativeL2ParticularValueCLM hκ0 hκ1 Vs
          (translated_kernel_bound V hminus s) (translated_kernel_bound V hplus s) Fs
        (vs : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
          (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) ∧
        MemWkp 2 2 vs nativePoissonEntranceCollar ∧
        (∀ j,HasWeakPartialDeriv j
          (nativeL2ParticularFirstCLM hκ0 hκ1 Vs (translated_kernel_bound V hminus s)
            (translated_kernel_bound V hplus s) j Fs) vs nativePoissonEntranceCollar) ∧
        (∀ k j,HasWeakPartialDeriv k
          (nativeL2ParticularSecondCLM hκ0 hκ1 Vs (translated_kernel_bound V hminus s)
            (translated_kernel_bound V hplus s) k j Fs)
          (nativeL2ParticularFirstCLM hκ0 hκ1 Vs (translated_kernel_bound V hminus s)
            (translated_kernel_bound V hplus s) j Fs) nativePoissonEntranceCollar) := by
  let W := nativeL2ParticularAngularCLM V F
  let w := nativeConjugatedJoint W
  have hw := nativeConjugatedJoint_measurable W
  have hae := nativeConjugatedJoint_ae W
  refine ⟨w,hw,hae,fun s => ?_⟩
  dsimp only
  refine ⟨?_,nativeL2ParticularCLM_memH2 hκ0 hκ1 _ _ _ _,
    nativeL2ParticularCLM_weak_jets hκ0 hκ1 _ _ _ _⟩
  have he := weightedCylinderShift_representation s hae
  have ht := nativeL2ParticularAngular_translate hκ0 hκ1 V hminus hplus s F
  have hs : ∀ t,(fun θ => weightedCylinderShift s w (t,θ))=ᵐ[angularVolume]
      (nativeConjugatedCurve (nativeL2ParticularAngularCLM (boundedTimeTranslate ℝ s V)
        (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F)) t : S → ℝ) := by
    intro t
    rw [ht,nativeConjugatedCurve_translate]
    exact he t
  have h := nativeL2ParticularValueCLM_eq_lift hκ0 hκ1 (boundedTimeTranslate ℝ s V)
    (translated_kernel_bound V hminus s) (translated_kernel_bound V hplus s)
    (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F) (weightedCylinderShift_measurable s hw) hs
  filter_upwards [h] with x hx
  exact hx.trans (cylinderLift_weightedCylinderShift s w x)

 theorem exists_nativeL2_all_shifted_collar_uniform_bounds :
    ∃ (C G : ℝ) (K : Fin 3 → ℝ),0≤C ∧ 0≤G ∧ (∀ k,0≤K k) ∧
      ∀ (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) (s : ℝ),
      let Vs := boundedTimeTranslate ℝ s V
      let Fs := l2TimeTranslateCLM (SpectralSpace AngularIndex) s F
      ‖nativeL2ParticularValueCLM hκ0 hκ1 Vs (translated_kernel_bound V hminus s)
        (translated_kernel_bound V hplus s) Fs‖≤C*‖F‖ ∧
      (∀ j,‖nativeL2ParticularFirstCLM hκ0 hκ1 Vs (translated_kernel_bound V hminus s)
        (translated_kernel_bound V hplus s) j Fs‖≤G*‖F‖) ∧
      (∀ k j,‖nativeL2ParticularSecondCLM hκ0 hκ1 Vs (translated_kernel_bound V hminus s)
        (translated_kernel_bound V hplus s) k j Fs‖≤K k*‖F‖) := by
  obtain ⟨C,G,K,hC,hG,hK,h⟩ := exists_uniform_nativeL2Particular_collar_bounds hκ0 hκ1 (norm_nonneg V)
  refine ⟨C,G,K,hC,hG,hK,fun F s => ?_⟩
  have hs := h (boundedTimeTranslate ℝ s V) (le_of_eq (boundedTimeTranslate_norm ℝ s V))
    (translated_kernel_bound V hminus s) (translated_kernel_bound V hplus s)
    (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F)
  simpa only [l2TimeTranslate_norm] using hs

#print axioms nativeL2ParticularAngular_translate
#print axioms nativeConjugatedCurve_translate
#print axioms nativeL2ShiftedCollar_same_physical_function
#print axioms exists_nativeL2_all_shifted_collar_uniform_bounds
end Yamabe3.Analysis.SpherePolar
