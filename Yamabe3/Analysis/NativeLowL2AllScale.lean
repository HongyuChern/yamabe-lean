import Yamabe3.Analysis.NativeLowL2SameField
import Yamabe3.Analysis.LowL2Translation
import Yamabe3.Analysis.NativeL2ShiftedCollar

/-! Every scaled physical low collar is produced from one L2 source and
one canonical field. The bound is uniform before the orbit and scale. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
variable (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0 ≤ v t ∧ v t ≤ 1)

theorem lowAngularOperatorBCF_translate (s : ℝ) :
    lowAngularOperatorBCF (fun t => v (t+s)) (hv.comp (continuous_id.add continuous_const)) (fun t => hb (t+s))=
      boundedTimeTranslate (AngularSpectralSpace →L[ℝ] AngularSpectralSpace) s (lowAngularOperatorBCF v hv hb) := by
  apply BoundedContinuousFunction.ext
  intro t
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem nativeLowL2Angular_translate (s : ℝ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeLowL2AngularCLM (fun t => v (t+s)) (hv.comp (continuous_id.add continuous_const)) (fun t => hb (t+s))
      (l2TimeTranslateCLM AngularSpectralSpace s F)=boundedTimeTranslate AngularL2 s (nativeLowL2AngularCLM v hv hb F) := by
  apply BoundedContinuousFunction.ext
  intro t
  change nativeLowProjection (angularBasis.repr.symm (lowL2ContinuousCLM
    (lowAngularOperatorBCF (fun t => v (t+s)) (hv.comp (continuous_id.add continuous_const)) (fun t => hb (t+s)))
    (lowAngularOperatorBCF_norm_le _ _ _) (l2TimeTranslateCLM AngularSpectralSpace s F) t))=_
  have ht := lowL2Continuous_translate s (lowAngularOperatorBCF v hv hb)
    (lowAngularOperatorBCF_norm_le v hv hb) F
  simp only [←lowAngularOperatorBCF_translate v hv hb s] at ht
  rw [ht]
  rfl

def nativeLowL2AllScaleRawJetCLM (s : ℝ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] NativeCollarJet :=
  (nativeLowL2RawJetCLM (fun t => v (t+s)) (hv.comp (continuous_id.add continuous_const)) (fun t => hb (t+s))).comp
    (l2TimeTranslateCLM AngularSpectralSpace s)

def nativeLowL2AllScaleJetCLM (s : ℝ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] nativeCollarJetClosure :=
  (nativeLowL2JetCLM (fun t => v (t+s)) (hv.comp (continuous_id.add continuous_const)) (fun t => hb (t+s))).comp
    (l2TimeTranslateCLM AngularSpectralSpace s)

theorem nativeLowL2AllScale_same_field (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (s : ℝ) :
    ((nativeLowL2AllScaleRawJetCLM v hv hb s F).1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*s/2)*nativeLowL2PhysicalField v hv hb F (Real.exp (-s) • x)) := by
  let w := nativeLowL2Joint v hv hb F
  have hw : Measurable w := (nativeLowL2Joint_continuous v hv hb F).measurable
  have he := weightedCylinderShift_representation s (nativeLowL2Joint_ae v hv hb F)
  have hs : ∀ t,(fun θ => weightedCylinderShift s w (t,θ))=ᵐ[angularVolume]
      (nativeConjugatedCurve (nativeLowL2AngularCLM (fun t => v (t+s)) (hv.comp (continuous_id.add continuous_const))
        (fun t => hb (t+s)) (l2TimeTranslateCLM AngularSpectralSpace s F)) t : S → ℝ) := by
    intro t
    rw [nativeLowL2Angular_translate,nativeConjugatedCurve_translate]
    exact he t
  have hp := congrArg (fun L : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] NativeCollarL2 =>
    L (l2TimeTranslateCLM AngularSpectralSpace s F))
    (nativeLowL2Value_eq_physical (fun t => v (t+s)) (hv.comp (continuous_id.add continuous_const)) (fun t => hb (t+s)))
  change (nativeLowL2AllScaleRawJetCLM v hv hb s F).1=
    nativeConjugatedCollarLp (nativeLowL2AngularCLM (fun t => v (t+s)) (hv.comp (continuous_id.add continuous_const))
      (fun t => hb (t+s)) (l2TimeTranslateCLM AngularSpectralSpace s F)) at hp
  rw [hp]
  have ha := nativeConjugatedCollarLp_eq_lift _ (weightedCylinderShift_measurable s hw) hs
  filter_upwards [ha] with x hx
  exact hx.trans ((cylinderLift_weightedCylinderShift s w x).trans (by rw [←nativeLowL2Physical_eq_lift v hv hb F]))

theorem nativeLowL2AllScale_memH2 (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (s : ℝ) :
    MemWkp 2 2 (nativeLowL2AllScaleRawJetCLM v hv hb s F).1 nativePoissonEntranceCollar :=
  nativeCollarJetClosure_memH2 (nativeLowL2AllScaleJetCLM v hv hb s F)

omit v hv hb in
theorem exists_uniform_nativeLowL2AllScale_bound :
    ∃ B : ℝ,0 < B ∧ ∀ (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0 ≤ v t ∧ v t ≤ 1) (s : ℝ),
      ‖nativeLowL2AllScaleRawJetCLM v hv hb s‖ ≤ B := by
  obtain ⟨B,hB,h⟩ := exists_uniform_nativeLowL2RawJet_bound
  refine ⟨B,hB,fun v hv hb s => ContinuousLinearMap.opNorm_le_bound _ hB.le (fun F => ?_)⟩
  have hh := (nativeLowL2RawJetCLM (fun t => v (t+s)) (hv.comp (continuous_id.add continuous_const))
    (fun t => hb (t+s))).le_of_opNorm_le
    (h (fun t => v (t+s)) (hv.comp (continuous_id.add continuous_const)) (fun t => hb (t+s)))
    (l2TimeTranslateCLM AngularSpectralSpace s F)
  change ‖nativeLowL2RawJetCLM (fun t => v (t+s)) (hv.comp (continuous_id.add continuous_const))
    (fun t => hb (t+s)) (l2TimeTranslateCLM AngularSpectralSpace s F)‖ ≤ B*‖F‖
  simpa only [l2TimeTranslate_norm] using hh

#print axioms lowAngularOperatorBCF_translate
#print axioms nativeLowL2Angular_translate
#print axioms nativeLowL2AllScale_same_field
#print axioms nativeLowL2AllScale_memH2
#print axioms exists_uniform_nativeLowL2AllScale_bound
end Yamabe3.Analysis.SpherePolar
