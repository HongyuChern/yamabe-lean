import Yamabe3.Analysis.NativeBoundaryPoissonLinearity
import Yamabe3.Analysis.NativeSupportedOuterValueDecay

/-! Linearity of the actual exterior Poisson field on EVERY scale.
The same jointly measurable representatives and their physical dilation
are used before uniqueness of the actual weak jets is applied. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic

private theorem exterior_curve_add (P:NativeHighPotential) (a b:AngularH1) (t:ℝ) :
    nativePoissonExteriorCurve P (a+b) t=nativePoissonExteriorCurve P a t+nativePoissonExteriorCurve P b t :=
  nativePoissonReflectedCurve_add P a b (-t)
private theorem exterior_curve_smul (P:NativeHighPotential) (c:ℝ) (b:AngularH1) (t:ℝ) :
    nativePoissonExteriorCurve P (c • b) t=c • nativePoissonExteriorCurve P b t :=
  nativePoissonReflectedCurve_smul P c b (-t)
private theorem exterior_shifted_value_same_order (P:NativeHighPotential)
    (b:AngularH1) (hb:NativeAngularSpectralRegular (3/2) (angularEmbedding b))
    {w:ℝ×S→ℝ} (hw:Measurable w)
    (hae:∀t,(fun θ=>w (t,θ))=ᵐ[angularVolume](nativePoissonExteriorCurve P b t:S→ℝ)) (s:ℝ) :
    (nativeExteriorShiftedValue P s b:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x=>Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) :=
  nativeExteriorShiftedValue_same_field P s b hb hw hae

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable (P : NativeHighPotential)
  (T : X →L[ℝ] AngularH1)
  (hT : ∀x,NativeAngularSpectralRegular (3/2) (angularEmbedding (T x)))
  (s : ℝ)

private def boundaryJoint (F : X) : ℝ × S → ℝ :=
  (exists_joint_L2_representative_of_continuous (nativePoissonExteriorCurve_continuous P (T F))).choose
private theorem boundaryJoint_measurable (F : X) :
    Measurable (boundaryJoint P T F) :=
  (exists_joint_L2_representative_of_continuous (nativePoissonExteriorCurve_continuous P (T F))).choose_spec.1.measurable
private theorem boundaryJoint_ae (F : X) (t : ℝ) :
    (fun θ => boundaryJoint P T F (t,θ))=ᵐ[angularVolume] (nativePoissonExteriorCurve P (T F) t : S → ℝ) := by
  simpa only [boundaryJoint,Measure.restrict_univ] using
    (exists_joint_L2_representative_of_continuous (nativePoissonExteriorCurve_continuous P (T F))).choose_spec.2 t

include hT in
theorem nativeExteriorShiftedFamilyValue_add (F G : X) :
    nativeExteriorShiftedValue P s (T (F+G))=nativeExteriorShiftedValue P s (T F)+nativeExteriorShiftedValue P s (T G) := by
  let w := boundaryJoint P T F
  let z := boundaryJoint P T G
  have hae (t : ℝ) : (fun θ => w (t,θ)+z (t,θ))=ᵐ[angularVolume]
      (nativePoissonExteriorCurve P (T (F+G)) t : S → ℝ) := by
    rw [map_add,exterior_curve_add]
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp
      (Lp.coeFn_add (nativePoissonExteriorCurve P (T F) t) (nativePoissonExteriorCurve P (T G) t))
    filter_upwards [boundaryJoint_ae P T F t,boundaryJoint_ae P T G t,hc] with θ hF hG hc
    change w (t,θ)=_ at hF
    change z (t,θ)=_ at hG
    rw [hF,hG]
    exact (hc (mem_univ θ)).symm
  have h := exterior_shifted_value_same_order P (T (F+G)) (hT (F+G))
    ((boundaryJoint_measurable P T F).add (boundaryJoint_measurable P T G)) hae s
  change (nativeExteriorShiftedValue P s (T (F+G)) : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
    (fun x => Real.exp (3*s/2)*cylinderLift (fun p => w p+z p) (Real.exp (-s) • x)) at h
  rw [native_cylinderLift_add] at h
  apply Lp.ext
  filter_upwards [h,Lp.coeFn_add (nativeExteriorShiftedValue P s (T F)) (nativeExteriorShiftedValue P s (T G)),
    exterior_shifted_value_same_order P (T F) (hT F) (boundaryJoint_measurable P T F) (boundaryJoint_ae P T F) s,
    exterior_shifted_value_same_order P (T G) (hT G) (boundaryJoint_measurable P T G) (boundaryJoint_ae P T G) s] with x hx hc hF hG
  rw [hx,hc]
  simp only [Pi.add_apply]
  rw [hF,hG]
  ring

include hT in
theorem nativeExteriorShiftedFamilyValue_smul (c : ℝ) (F : X) :
    nativeExteriorShiftedValue P s (T (c•F))=c•nativeExteriorShiftedValue P s (T F) := by
  let w := boundaryJoint P T F
  have hae (t : ℝ) : (fun θ => c*w (t,θ))=ᵐ[angularVolume]
      (nativePoissonExteriorCurve P (T (c•F)) t : S → ℝ) := by
    rw [map_smul,exterior_curve_smul]
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp (Lp.coeFn_smul c (nativePoissonExteriorCurve P (T F) t))
    filter_upwards [boundaryJoint_ae P T F t,hc] with θ hF hc
    change w (t,θ)=_ at hF
    rw [hF]
    simpa only [Pi.smul_apply,smul_eq_mul] using (hc (mem_univ θ)).symm
  have h := exterior_shifted_value_same_order P (T (c•F)) (hT (c•F))
    (measurable_const.mul (boundaryJoint_measurable P T F)) hae s
  change (nativeExteriorShiftedValue P s (T (c•F)) : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
    (fun x => Real.exp (3*s/2)*cylinderLift (fun p => c*w p) (Real.exp (-s) • x)) at h
  rw [native_cylinderLift_smul] at h
  apply Lp.ext
  filter_upwards [h,Lp.coeFn_smul c (nativeExteriorShiftedValue P s (T F)),
    exterior_shifted_value_same_order P (T F) (hT F) (boundaryJoint_measurable P T F) (boundaryJoint_ae P T F) s] with x hx hc hF
  rw [hx,hc]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hF]
  ring

#print axioms exterior_curve_add
#print axioms exterior_curve_smul
#print axioms nativeExteriorShiftedFamilyValue_add
#print axioms nativeExteriorShiftedFamilyValue_smul
end Yamabe3.Analysis.SpherePolar
