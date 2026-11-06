import Yamabe3.Analysis.NativePoissonTailH2
import Yamabe3.Analysis.NativePoissonReflectedCurve

/-! The constructed tail jets represent the very same original Poisson
curve, for any actual joint representative. Only positive-time slice
identities are used on these collars. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

 theorem nativePoissonTailValue_same_field (P : NativeHighPotential)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
    (b : AngularH1) {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t,0 ≤ t → (fun θ => w (t,θ))=ᵐ[angularVolume] (P.curve b t : S → ℝ))
    (s : ℝ) (hs : 1 ≤ s) :
    (nativePoissonTailValue P hplus s b : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) := by
  let a := nativePoissonAuxiliary P b
  let F := nativePoissonL2CorrectionSource P b
  let Wf := nativeFreeBoundaryAngular a
  let Wc := nativeL2ParticularAngularCLM P.potential F
  let wf := nativeConjugatedJoint Wf
  let wc := nativeConjugatedJoint Wc
  have hwf := nativeConjugatedJoint_measurable Wf
  have hwc := nativeConjugatedJoint_measurable Wc
  have hef := nativeConjugatedJoint_ae Wf
  have hec := nativeConjugatedJoint_ae Wc
  have hfree := nativeFreeTailValue_same_dilation a hwf hef s hs
  have ht := nativeL2ParticularAngular_translate P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus s F
  have hcs : ∀ t,(fun θ => weightedCylinderShift s wc (t,θ))=ᵐ[angularVolume]
      (nativeConjugatedCurve (nativeL2ParticularAngularCLM (boundedTimeTranslate ℝ s P.potential)
        (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F)) t : S → ℝ) := by
    intro t
    rw [ht,nativeConjugatedCurve_translate]
    exact weightedCylinderShift_representation s hec t
  have hcorr0 := nativeL2ParticularValueCLM_eq_lift P.κ_nonneg P.κ_lt_one
    (boundedTimeTranslate ℝ s P.potential) (translated_kernel_bound P.potential P.kernel_bound s)
    (translated_kernel_bound P.potential hplus s) (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F)
    (weightedCylinderShift_measurable s hwc) hcs
  have hsame (t : ℝ) (ht0 : 0 ≤ t) :
      (fun θ => wf (t,θ)-wc (t,θ))=ᵐ[angularVolume] (fun θ => w (t,θ)) := by
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp
      (Lp.coeFn_sub (nativeConjugatedCurve Wf t) (nativeConjugatedCurve Wc t))
    have hp := nativePoissonCurve_same_L2_correction P hplus b t ht0
    filter_upwards [hef t,hec t,hae t ht0,hc] with θ hf hc hw hsub
    change wf (t,θ)=_ at hf
    change wc (t,θ)=_ at hc
    rw [hf,hc,hw,hp]
    exact (hsub (mem_univ θ)).symm
  have hlocal := native_collar_lift_ae_eq_of_local_slices
    (weightedCylinderShift_measurable s (hwf.sub hwc)) (weightedCylinderShift_measurable s hw)
    (fun t ht => by
      have hts : 0 ≤ t+s := by linarith [ht.1]
      filter_upwards [hsame (t+s) hts] with θ hθ
      change Real.exp (2*s)*(wf (t+s,θ)-wc (t+s,θ))=Real.exp (2*s)*w (t+s,θ)
      rw [hθ])
  have hsub := Lp.coeFn_sub (nativeFreeTailValue s a)
    (nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one (boundedTimeTranslate ℝ s P.potential)
      (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hplus s)
      (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F))
  filter_upwards [hfree,hcorr0,hlocal,hsub] with x hf hc hl hsub
  change (nativeFreeTailValue s a-_) x=_
  rw [hsub]
  change nativeFreeTailValue s a x-_=_
  rw [hf,hc,cylinderLift_weightedCylinderShift]
  have he := cylinderLift_weightedCylinderShift s (fun p => wf p-wc p) x
  rw [cylinderLift_sub] at he
  change cylinderLift (weightedCylinderShift s (fun p => wf p-wc p)) x=cylinderLift (weightedCylinderShift s w) x at hl
  rw [he,cylinderLift_weightedCylinderShift] at hl
  change Real.exp (3*s/2)*(cylinderLift wf (Real.exp (-s) • x)-cylinderLift wc (Real.exp (-s) • x))=_ at hl
  exact (by rw [mul_sub] at hl;exact hl)

#print axioms nativePoissonTailValue_same_field
end Yamabe3.Analysis.SpherePolar
