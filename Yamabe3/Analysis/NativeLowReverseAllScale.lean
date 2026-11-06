import Yamabe3.Analysis.NativeLowReverseL2SameField
import Yamabe3.Analysis.NativeLowL2AllScale
import Yamabe3.Analysis.NativeAllScaleLocalH2

/-! Every exterior low-mode scale is the same reversed canonical field.
The physical scale factor exp(4s) is retained, giving a decaying H2 collar
bound toward negative time and genuine local H2 away from the origin. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
variable (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)

theorem nativeLowReverseL2Joint_shift (s : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    weightedCylinderShift s (nativeLowReverseL2Joint v hv hb F)=
      fun z => Real.exp (4*s)*nativeLowReverseL2Joint (fun t => v (t+ -s))
        (hv.comp (continuous_id.add continuous_const)) (fun t => hb (t+ -s))
        (l2TimeTranslateCLM AngularSpectralSpace (-s) F) z := by
  have ht := lowL2Continuous_translate (-s) (lowAngularOperatorBCF v hv hb)
    (lowAngularOperatorBCF_norm_le v hv hb) F
  simp only [←lowAngularOperatorBCF_translate v hv hb (-s)] at ht
  funext z
  simp only [weightedCylinderShift,nativeLowReverseL2Joint,finiteAngular,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ht]
  change Real.exp (2*s)*(Real.exp (2*(z.1+s))*
    lowL2ContinuousCLM (lowAngularOperatorBCF v hv hb) (lowAngularOperatorBCF_norm_le v hv hb) F (-(z.1+s)) i*
      angularRepresentative i z.2)=Real.exp (4*s)*(Real.exp (2*z.1)*
    lowL2ContinuousCLM (lowAngularOperatorBCF v hv hb) (lowAngularOperatorBCF_norm_le v hv hb) F (-z.1+ -s) i*
      angularRepresentative i z.2)
  rw [show -(z.1+s)= -z.1+ -s by ring]
  have he : Real.exp (2*s)*Real.exp (2*(z.1+s))=Real.exp (4*s)*Real.exp (2*z.1) := by
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (2*s)*Real.exp (2*(z.1+s)))*
      lowL2ContinuousCLM (lowAngularOperatorBCF v hv hb) (lowAngularOperatorBCF_norm_le v hv hb) F (-z.1+ -s) i*
        angularRepresentative i z.2 := by ring
    _ = _ := by rw [he];ring

def nativeLowReverseAllScaleJetCLM (s : ℝ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] nativeCollarJetClosure :=
  Real.exp (4*s) • ((nativeLowReverseL2JetCLM (fun t => v (t+ -s))
    (hv.comp (continuous_id.add continuous_const)) (fun t => hb (t+ -s))).comp
      (l2TimeTranslateCLM AngularSpectralSpace (-s)))

def nativeLowReverseAllScaleRawJetCLM (s : ℝ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] NativeCollarJet :=
  nativeCollarJetClosure.subtypeL.comp (nativeLowReverseAllScaleJetCLM v hv hb s)

theorem nativeLowReverseAllScale_same_field (s : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    ((nativeLowReverseAllScaleRawJetCLM v hv hb s F).1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*s/2)*nativeLowReverseL2PhysicalField v hv hb F (Real.exp (-s) • x)) := by
  let vs := fun t => v (t+ -s)
  let hvs : Continuous vs := hv.comp (continuous_id.add continuous_const)
  let hbs := fun t => hb (t+ -s)
  let Fs := l2TimeTranslateCLM AngularSpectralSpace (-s) F
  have he (x : E) : Real.exp (4*s)*nativeLowReverseL2PhysicalField vs hvs hbs Fs x=
      Real.exp (3*s/2)*nativeLowReverseL2PhysicalField v hv hb F (Real.exp (-s) • x) := by
    rw [nativeLowReverseL2Physical_eq_lift,nativeLowReverseL2Physical_eq_lift]
    rw [←cylinderLift_weightedCylinderShift,nativeLowReverseL2Joint_shift,native_cylinderLift_smul]
  have h := nativeLowReverseL2Value_same_field vs hvs hbs Fs
  change ((Real.exp (4*s) • (nativeLowReverseL2RawJetCLM vs hvs hbs Fs).1 : NativeCollarL2) : E→ℝ)=ᵐ[_] _
  filter_upwards [Lp.coeFn_smul (Real.exp (4*s)) (nativeLowReverseL2RawJetCLM vs hvs hbs Fs).1,h] with x hx hf
  rw [hx]
  change Real.exp (4*s)*(nativeLowReverseL2RawJetCLM vs hvs hbs Fs).1 x=_
  rw [hf]
  exact he x

theorem nativeLowReverseAllScale_memH2 (s : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    MemWkp 2 2 (nativeLowReverseAllScaleRawJetCLM v hv hb s F).1 nativePoissonEntranceCollar :=
  nativeCollarJetClosure_memH2 (nativeLowReverseAllScaleJetCLM v hv hb s F)

theorem nativeLowReversePhysical_localH2 (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    MemWkpLocally 2 (nativeLowReverseL2PhysicalField v hv hb F) ({0}ᶜ : Set E) :=
  native_all_scale_H2_local (fun s =>
    (MemWkp_congr_ae (by norm_num) (nativePolarTimeWindow_open (1/2))
      (nativeLowReverseAllScale_same_field v hv hb s F)).mp (nativeLowReverseAllScale_memH2 v hv hb s F))

omit v hv hb in
theorem exists_uniform_nativeLowReverseAllScale_bound :
    ∃B : ℝ,0<B ∧ ∀(v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1) (s : ℝ),
      ‖nativeLowReverseAllScaleRawJetCLM v hv hb s‖≤B*Real.exp (4*s) := by
  obtain ⟨B,hB,hd⟩ := exists_uniform_nativeLowReverseL2RawJet_bound
  refine ⟨B,hB,fun v hv hb s => ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun F => ?_)⟩
  change ‖Real.exp (4*s) • nativeLowReverseL2RawJetCLM (fun t => v (t+ -s))
    (hv.comp (continuous_id.add continuous_const)) (fun t => hb (t+ -s))
      (l2TimeTranslateCLM AngularSpectralSpace (-s) F)‖≤_
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
  have hh := (nativeLowReverseL2RawJetCLM (fun t => v (t+ -s))
    (hv.comp (continuous_id.add continuous_const)) (fun t => hb (t+ -s))).le_of_opNorm_le
      (hd _ _ _) (l2TimeTranslateCLM AngularSpectralSpace (-s) F)
  rw [l2TimeTranslate_norm] at hh
  exact (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le).trans_eq (by ring)

#print axioms nativeLowReverseL2Joint_shift
#print axioms nativeLowReverseAllScale_same_field
#print axioms nativeLowReverseAllScale_memH2
#print axioms nativeLowReversePhysical_localH2
#print axioms exists_uniform_nativeLowReverseAllScale_bound
end Yamabe3.Analysis.SpherePolar
