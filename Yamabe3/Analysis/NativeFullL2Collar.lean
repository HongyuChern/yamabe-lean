import Yamabe3.Analysis.NativeLowL2PhysicalEquation
import Yamabe3.Analysis.NativeLowL2AllScale
import Yamabe3.Analysis.NativeFamilyGeometricRows

/-! High zero-entrance and low future solutions of one L2 source are
combined in the same strong H2 jet closure. The low entrance is retained.
A same-potential equality is explicit here and is discharged for the
actual orbit in the subsequent specialization. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
variable (P : NativeHighPotential)
  (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0≤v t ∧ v t≤1)

def nativeFullL2AllScaleRawJetCLM (s : ℝ) : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] NativeCollarJet :=
  nativeL2HalfAllScaleRawJetCLM P hp s+nativeLowL2AllScaleRawJetCLM v hv hb s

def nativeFullL2AllScaleJetCLM (s : ℝ) : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] nativeCollarJetClosure :=
  nativeL2HalfAllScaleJetCLM P hp s+nativeLowL2AllScaleJetCLM v hv hb s

theorem nativeFullL2AllScale_memH2 (s : ℝ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    MemWkp 2 2 (nativeFullL2AllScaleRawJetCLM P hp v hv hb s F).1 nativePoissonEntranceCollar :=
  nativeCollarJetClosure_memH2 (nativeFullL2AllScaleJetCLM P hp v hv hb s F)

theorem nativeLowL2AllScale_equation (s : ℝ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    (∑ j : Fin 3,(nativeLowL2AllScaleRawJetCLM v hv hb s F).2.2 j j)+
      nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s (delaunayPhasePotentialBCF v hv hb 0))
        (nativeLowL2AllScaleRawJetCLM v hv hb s F).1=
      nativeL2LowPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F) := by
  have he : delaunayPhasePotentialBCF (fun t => v (t+s))
      (hv.comp (continuous_id.add continuous_const)) (fun t => hb (t+s)) 0=
      boundedTimeTranslate ℝ s (delaunayPhasePotentialBCF v hv hb 0) := by
    apply BoundedContinuousFunction.ext
    intro t
    change (15/4)*v (t+0+s)^4=(15/4)*v (t+s+0)^4
    simp only [add_zero]
  have h := nativeLowL2_physical_equation (fun t => v (t+s))
    (hv.comp (continuous_id.add continuous_const)) (fun t => hb (t+s)) (l2TimeTranslateCLM AngularSpectralSpace s F)
  rw [he] at h
  exact h

theorem nativeFullL2AllScale_equation
    (hpot : P.potential=delaunayPhasePotentialBCF v hv hb 0)
    (s : ℝ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativePositiveScaledRestrictionCLM s
      ((∑ j : Fin 3,(nativeFullL2AllScaleRawJetCLM P hp v hv hb s F).2.2 j j)+
        nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s P.potential)
          (nativeFullL2AllScaleRawJetCLM P hp v hv hb s F).1)=
      nativePositiveScaledRestrictionCLM s (nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F)) := by
  let H := nativeL2HalfAllScaleRawJetCLM P hp s F
  let L := nativeLowL2AllScaleRawJetCLM v hv hb s F
  let V := boundedTimeTranslate ℝ s P.potential
  have hh := nativeL2HalfAllScale_physical_equation P hp s F
  have hl := nativeLowL2AllScale_equation v hv hb s F
  rw [←hpot] at hl
  change nativePositiveScaledRestrictionCLM s
    ((∑ j : Fin 3,(H.2.2 j j+L.2.2 j j))+nativeCollarPotentialMulCLM V (H.1+L.1))=_
  rw [Finset.sum_add_distrib,(nativeCollarPotentialMulCLM V).map_add]
  have he : ((∑ j : Fin 3,H.2.2 j j)+(∑ j : Fin 3,L.2.2 j j))+
      (nativeCollarPotentialMulCLM V H.1+nativeCollarPotentialMulCLM V L.1)=
      ((∑ j : Fin 3,H.2.2 j j)+nativeCollarPotentialMulCLM V H.1)+
        ((∑ j : Fin 3,L.2.2 j j)+nativeCollarPotentialMulCLM V L.1) := by abel
  change nativePositiveScaledRestrictionCLM s
    ((∑ j : Fin 3,H.2.2 j j)+nativeCollarPotentialMulCLM V H.1)=
      nativePositiveScaledRestrictionCLM s (nativeL2HighPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F)) at hh
  change (∑ j : Fin 3,L.2.2 j j)+nativeCollarPotentialMulCLM V L.1=
    nativeL2LowPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F) at hl
  rw [he,map_add,hh,hl,←map_add,nativeL2High_add_low_source]

theorem exists_nativeFullL2AllScale_same_field (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    ∃ w : ℝ × S → ℝ,Measurable w ∧ ∀ s : ℝ,
      ((nativeFullL2AllScaleRawJetCLM P hp v hv hb s F).1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) := by
  obtain ⟨_,w,hw,hae,hjet⟩ := nativeL2HalfAllScale_same_field_H2_zero_entrance P hp F
  let z := nativeLowL2Joint v hv hb F
  refine ⟨fun p => w p+z p,hw.measurable.add (nativeLowL2Joint_continuous v hv hb F).measurable,fun s => ?_⟩
  have hl := nativeLowL2AllScale_same_field v hv hb F s
  have ha := Lp.coeFn_add (nativeL2HalfAllScaleValue P hp s F) (nativeLowL2AllScaleRawJetCLM v hv hb s F).1
  filter_upwards [(hjet s).1,hl,ha] with x hh hl ha
  change (nativeL2HalfAllScaleValue P hp s F+(nativeLowL2AllScaleRawJetCLM v hv hb s F).1) x=_
  rw [ha]
  change nativeL2HalfAllScaleValue P hp s F x+(nativeLowL2AllScaleRawJetCLM v hv hb s F).1 x=_
  rw [hh,hl,nativeLowL2Physical_eq_lift]
  rw [native_cylinderLift_add]
  exact (mul_add _ _ _).symm

omit P hp v hv hb in
theorem exists_family_nativeFullL2AllScale_bound {κ M : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (hM : 0≤M) :
    ∃ B : ℝ,0<B ∧ ∀ (P : NativeHighPotential),P.κ=κ → ‖P.potential‖≤M →
      ∀ (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ),
      ∀ (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0≤v t ∧ v t≤1) (s : ℝ),
        ‖nativeFullL2AllScaleRawJetCLM P hp v hv hb s‖≤B := by
  obtain ⟨H,hH,hh⟩ := exists_family_nativeL2HalfAllScale_raw_jet_bound hκ0 hκ1 hM
  obtain ⟨L,hL,hl⟩ := exists_uniform_nativeLowL2AllScale_bound
  exact ⟨H+L,by positivity,fun P hP hPM hp v hv hb s =>
    (norm_add_le _ _).trans (add_le_add (hh P hP hPM hp s) (hl v hv hb s))⟩

#print axioms nativeFullL2AllScale_memH2
#print axioms nativeLowL2AllScale_equation
#print axioms nativeFullL2AllScale_equation
#print axioms exists_nativeFullL2AllScale_same_field
#print axioms exists_family_nativeFullL2AllScale_bound
end Yamabe3.Analysis.SpherePolar
