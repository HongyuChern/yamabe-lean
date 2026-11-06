import Yamabe3.Analysis.NativeL2HalfAllScaleH2

/-! Every collar represents one fixed half-end field. The actual entrance
and the previously constructed weak jets are retained at scale zero. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

variable (P : NativeHighPotential)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)

theorem nativeL2HalfAllScaleValue_same_field
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ))
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume] (nativeL2HalfCollarCurve P hplus F t : S → ℝ)) (s : ℝ) :
    (nativeL2HalfAllScaleValue P hplus s F : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) := by
  obtain ⟨v,hv,hva,hvals⟩ := nativeL2ShiftedCollar_same_physical_function
    P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F
  obtain ⟨z,hz,hza,_⟩ := nativePoissonReflectedCurve_joint_representative P (nativeL2HalfEntrance P hplus F)
  have hzv := nativePoissonAllScaleValue_same_field P hplus _
    (nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F).2.1 hz.measurable hza s
  have hvv := (hvals s).1
  have hsame (t : ℝ) : (fun θ => v (t,θ)-z (t,θ))=ᵐ[angularVolume] (fun θ => w (t,θ)) := by
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp
      (Lp.coeFn_sub (nativeConjugatedCurve (nativeL2ParticularAngularCLM P.potential F) t)
        (nativePoissonReflectedCurve P (nativeL2HalfEntrance P hplus F) t))
    filter_upwards [hva t,hza t,hae t,hc] with θ hv hz hw hc
    rw [hv,hz,hw]
    exact (hc (mem_univ θ)).symm
  have hrep := native_collar_lift_ae_eq_of_joint_slices
    (weightedCylinderShift_measurable s (hv.sub hz.measurable)) (weightedCylinderShift_measurable s hw)
    (fun t => by
      filter_upwards [hsame (t+s)] with θ hθ
      change Real.exp (2*s)*(v (t+s,θ)-z (t+s,θ))=Real.exp (2*s)*w (t+s,θ)
      rw [hθ])
  have hsub := Lp.coeFn_sub
    (nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one (boundedTimeTranslate ℝ s P.potential)
      (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hplus s)
      (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F))
    (nativePoissonAllScaleValue P hplus s (nativeL2HalfEntrance P hplus F))
  filter_upwards [hvv,hzv,hrep,hsub] with x hv hz hr hc
  change (_-nativePoissonAllScaleValue P hplus s (nativeL2HalfEntrance P hplus F)) x=_
  rw [hc]
  simp only [Pi.sub_apply]
  change nativePoissonAllScaleValue P hplus s (nativeL2HalfEntrance P hplus F) x=Real.exp (3*s/2)*cylinderLift z (Real.exp (-s) • x) at hz
  rw [hv,hz]
  have he := cylinderLift_weightedCylinderShift s (fun p => v p-z p) x
  rw [cylinderLift_sub] at he
  change cylinderLift (weightedCylinderShift s (fun p => v p-z p)) x=cylinderLift (weightedCylinderShift s w) x at hr
  rw [he,cylinderLift_weightedCylinderShift] at hr
  change Real.exp (3*s/2)*(cylinderLift v (Real.exp (-s) • x)-cylinderLift z (Real.exp (-s) • x))=_ at hr
  exact (by rw [mul_sub] at hr;exact hr)

theorem nativeL2HalfAllScale_same_field_H2_zero_entrance
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeL2HalfCollarCurve P hplus F 0=0 ∧
    ∃ w : ℝ × S → ℝ,StronglyMeasurable w ∧
      (∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume] (nativeL2HalfCollarCurve P hplus F t : S → ℝ)) ∧
      ∀ s : ℝ,
        (nativeL2HalfAllScaleValue P hplus s F : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
          (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) ∧
        MemWkp 2 2 (nativeL2HalfAllScaleValue P hplus s F) nativePoissonEntranceCollar ∧
        (∀ j,HasWeakPartialDeriv j (nativeL2HalfAllScaleFirst P hplus s F j)
          (nativeL2HalfAllScaleValue P hplus s F) nativePoissonEntranceCollar) ∧
        (∀ k j,HasWeakPartialDeriv k (nativeL2HalfAllScaleSecond P hplus s F k j)
          (nativeL2HalfAllScaleFirst P hplus s F j) nativePoissonEntranceCollar) := by
  obtain ⟨hzero,w,hw,hae,_⟩ := exists_nativeL2Half_same_field_H2_zero_entrance P hplus F
  exact ⟨hzero,w,hw,hae,fun s => ⟨nativeL2HalfAllScaleValue_same_field P hplus F hw.measurable hae s,
    nativeL2HalfAllScale_H2_same_jets P hplus s F⟩⟩

theorem nativeL2HalfAllScale_zero_eq_original
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeL2HalfAllScaleValue P hplus 0 F=nativeL2HalfCollarValue P hplus F ∧
    (∀ j,nativeL2HalfAllScaleFirst P hplus 0 F j=nativeL2HalfCollarFirst P hplus F j) ∧
    (∀ k j,nativeL2HalfAllScaleSecond P hplus 0 F k j=nativeL2HalfCollarSecond P hplus F k j) := by
  obtain ⟨_,w,hw,hae,hval,_⟩ := exists_nativeL2Half_same_field_H2_zero_entrance P hplus F
  have hs := nativeL2HalfAllScaleValue_same_field P hplus F hw.measurable hae 0
  have hv : nativeL2HalfAllScaleValue P hplus 0 F=nativeL2HalfCollarValue P hplus F := by
    apply Lp.ext
    have hs0 : (nativeL2HalfAllScaleValue P hplus 0 F : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w := by
      simpa only [mul_zero,zero_div,neg_zero,Real.exp_zero,one_mul,one_smul] using hs
    exact hs0.trans hval.symm
  have hn := nativeL2HalfAllScale_H2_same_jets P hplus 0 F
  have ho := nativeL2HalfCollar_H2_and_jets P hplus F
  have h1 (j : Fin 3) : nativeL2HalfAllScaleFirst P hplus 0 F j=nativeL2HalfCollarFirst P hplus F j := by
    apply Lp.ext
    have h := hn.2.1 j
    rw [hv] at h
    exact h.ae_eq (nativePolarTimeWindow_open (1/2)) (ho.2.1 j)
      ((Lp.memLp _).locallyIntegrable (by norm_num)) ((Lp.memLp _).locallyIntegrable (by norm_num))
  refine ⟨hv,h1,fun k j => ?_⟩
  apply Lp.ext
  have h := hn.2.2 k j
  rw [h1 j] at h
  exact h.ae_eq (nativePolarTimeWindow_open (1/2)) (ho.2.2 k j)
    ((Lp.memLp _).locallyIntegrable (by norm_num)) ((Lp.memLp _).locallyIntegrable (by norm_num))

#print axioms nativeL2HalfAllScaleValue_same_field
#print axioms nativeL2HalfAllScale_same_field_H2_zero_entrance
#print axioms nativeL2HalfAllScale_zero_eq_original
end Yamabe3.Analysis.SpherePolar
