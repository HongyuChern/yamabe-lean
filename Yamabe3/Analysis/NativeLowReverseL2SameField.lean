import Yamabe3.Analysis.NativeLowReverseL2Extension
import Yamabe3.Analysis.NativeLowL2SameField
import Yamabe3.Analysis.NativeReverseConjugatedCollarLift
import Yamabe3.Analysis.NativeAngularInverseLinearity

/-! The all-L2 low H2 jet is the lift of the same canonical solution.
The joint representative is an explicit finite angular sum; no arbitrary
volume representative is restricted to a sphere. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Euclidean
variable (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0 ≤ v t ∧ v t ≤ 1)

def nativeLowReverseL2Joint (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) : ℝ × S → ℝ :=
  finiteAngular nativeLowIndexFinset (fun i t => Real.exp (2*t)*
    lowL2ContinuousCLM (lowAngularOperatorBCF v hv hb) (lowAngularOperatorBCF_norm_le v hv hb) F (-t) i)

theorem nativeLowReverseL2Joint_continuous (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    Continuous (nativeLowReverseL2Joint v hv hb F) := by
  let U := lowL2ContinuousCLM (lowAngularOperatorBCF v hv hb) (lowAngularOperatorBCF_norm_le v hv hb) F
  apply continuous_finset_sum
  intro i _
  have hUi : Continuous (fun t => U t i) :=
    (lp.evalCLM ℝ (fun _ : AngularIndex => ℝ) 2 i).continuous.comp U.continuous
  exact (((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
    (hUi.comp continuous_fst.neg)).mul ((smooth_angularRepresentative i).continuous.comp continuous_snd))

theorem nativeLowReverseL2Joint_ae (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (t : ℝ) :
    (fun θ => nativeLowReverseL2Joint v hv hb F (t,θ))=ᵐ[angularVolume]
      (nativeReverseConjugatedCurve (nativeLowL2AngularCLM v hv hb F) t : S → ℝ) := by
  let U := lowL2ContinuousCLM (lowAngularOperatorBCF v hv hb) (lowAngularOperatorBCF_norm_le v hv hb) F
  have he : (∑ i ∈ nativeLowIndexFinset,(Real.exp (2*t)*U (-t) i) • angularBasis i)=
      nativeReverseConjugatedCurve (nativeLowL2AngularCLM v hv hb F) t := by
    change _=Real.exp (2*t) • nativeLowProjection (angularBasis.repr.symm (U (-t)))
    rw [nativeLowProjection_eq_finite,finiteHilbertProjection,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [←HilbertBasis.repr_apply_apply,LinearIsometryEquiv.apply_symm_apply,mul_smul]
  have h := finiteAngular_ae nativeLowIndexFinset (fun i s => Real.exp (2*s)*U (-s) i) t
  rw [he] at h
  exact h

theorem nativeLowReverseL2Physical_eq_lift (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeLowReverseL2PhysicalField v hv hb F=cylinderLift (nativeLowReverseL2Joint v hv hb F) :=
  finitePhysical_eq_lift _ _

theorem nativeLowReverseL2Value_eq_physical :
    nativeCollarJetValueCLM.comp (nativeLowReverseL2RawJetCLM v hv hb)=
      nativeReverseConjugatedCollarCLM.comp (nativeLowL2AngularCLM v hv hb) := by
  apply ContinuousLinearMap.ext
  intro F
  have hc := isClosed_eq (nativeCollarJetValueCLM.comp (nativeLowReverseL2RawJetCLM v hv hb)).continuous
    (nativeReverseConjugatedCollarCLM.comp (nativeLowL2AngularCLM v hv hb)).continuous
  refine (continuousL2SourceInclusion_dense AngularSpectralSpace).induction_on F hc ?_
  intro H
  change (nativeLowReverseL2RawJetCLM v hv hb (continuousL2SourceInclusion _ H)).1=_
  rw [nativeLowReverseL2RawJet_agrees_continuous]
  apply Lp.ext
  have h := (nativeC2Collar_memLp (nativeLowReverseL2Physical_collar_energy v hv hb H.val H.property).1).1.coeFn_toLp
  have hl := nativeReverseConjugatedCollarLp_eq_lift (nativeLowL2AngularCLM v hv hb (continuousL2SourceInclusion _ H))
    (nativeLowReverseL2Joint_continuous v hv hb _).measurable (nativeLowReverseL2Joint_ae v hv hb _)
  rw [←nativeLowReverseL2Physical_eq_lift v hv hb] at hl
  exact h.trans hl.symm

theorem nativeLowReverseL2Value_same_field (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    ((nativeLowReverseL2RawJetCLM v hv hb F).1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      nativeLowReverseL2PhysicalField v hv hb F := by
  have he := congrArg (fun L : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] NativeCollarL2 => L F)
    (nativeLowReverseL2Value_eq_physical v hv hb)
  change (nativeLowReverseL2RawJetCLM v hv hb F).1=nativeReverseConjugatedCollarLp (nativeLowL2AngularCLM v hv hb F) at he
  rw [he,nativeLowReverseL2Physical_eq_lift v hv hb]
  exact nativeReverseConjugatedCollarLp_eq_lift _ (nativeLowReverseL2Joint_continuous v hv hb F).measurable
    (nativeLowReverseL2Joint_ae v hv hb F)

#print axioms nativeLowReverseL2Joint_continuous
#print axioms nativeLowReverseL2Joint_ae
#print axioms nativeLowReverseL2Physical_eq_lift
#print axioms nativeLowReverseL2Value_eq_physical
#print axioms nativeLowReverseL2Value_same_field
end Yamabe3.Analysis.SpherePolar
