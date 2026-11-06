import Yamabe3.Analysis.NativeBoundaryPoissonLinearity
import Yamabe3.Analysis.NativePoissonExteriorCollarIdentification
import Yamabe3.Analysis.NativeCollarJetValueInjective

/-! Linearity of the actual reversed-time exterior Poisson field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

private theorem nativePoissonExteriorCurve_add (P : NativeHighPotential) (a b : AngularH1) (t : ℝ) :
    nativePoissonExteriorCurve P (a+b) t=nativePoissonExteriorCurve P a t+nativePoissonExteriorCurve P b t :=
  nativePoissonReflectedCurve_add P a b (-t)
private theorem nativePoissonExteriorCurve_smul (P : NativeHighPotential) (c : ℝ) (b : AngularH1) (t : ℝ) :
    nativePoissonExteriorCurve P (c•b) t=c•nativePoissonExteriorCurve P b t :=
  nativePoissonReflectedCurve_smul P c b (-t)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable (P : NativeHighPotential)
  (T : X →L[ℝ] AngularH1)
  (hT : ∀x,NativeAngularSpectralRegular (3/2) (angularEmbedding (T x)))

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
theorem nativeExteriorBoundaryValue_add (F G : X) :
    nativePoissonExteriorCollarValue P (T (F+G))=nativePoissonExteriorCollarValue P (T F)+nativePoissonExteriorCollarValue P (T G) := by
  let w := boundaryJoint P T F
  let z := boundaryJoint P T G
  have hae (t : ℝ) : (fun θ => w (t,θ)+z (t,θ))=ᵐ[angularVolume]
      (nativePoissonExteriorCurve P (T (F+G)) t : S → ℝ) := by
    rw [map_add,nativePoissonExteriorCurve_add]
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp
      (Lp.coeFn_add (nativePoissonExteriorCurve P (T F) t) (nativePoissonExteriorCurve P (T G) t))
    filter_upwards [boundaryJoint_ae P T F t,boundaryJoint_ae P T G t,hc] with θ hF hG hc
    change w (t,θ)=_ at hF
    change z (t,θ)=_ at hG
    rw [hF,hG]
    exact (hc (mem_univ θ)).symm
  have h := nativePoissonExteriorCollarValue_eq_lift P (T (F+G)) (hT (F+G))
    ((boundaryJoint_measurable P T F).add (boundaryJoint_measurable P T G)) hae
  change (nativePoissonExteriorCollarValue P (T (F+G)) : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
    cylinderLift (fun p => w p+z p) at h
  rw [native_cylinderLift_add] at h
  apply Lp.ext
  filter_upwards [h,Lp.coeFn_add (nativePoissonExteriorCollarValue P (T F)) (nativePoissonExteriorCollarValue P (T G)),
    nativePoissonExteriorCollarValue_eq_lift P (T F) (hT F) (boundaryJoint_measurable P T F) (boundaryJoint_ae P T F),
    nativePoissonExteriorCollarValue_eq_lift P (T G) (hT G) (boundaryJoint_measurable P T G) (boundaryJoint_ae P T G)] with x hx hc hF hG
  rw [hx,hc]
  simp only [Pi.add_apply]
  rw [hF,hG]

include hT in
theorem nativeExteriorBoundaryValue_smul (c : ℝ) (F : X) :
    nativePoissonExteriorCollarValue P (T (c•F))=c•nativePoissonExteriorCollarValue P (T F) := by
  let w := boundaryJoint P T F
  have hae (t : ℝ) : (fun θ => c*w (t,θ))=ᵐ[angularVolume]
      (nativePoissonExteriorCurve P (T (c•F)) t : S → ℝ) := by
    rw [map_smul,nativePoissonExteriorCurve_smul]
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp (Lp.coeFn_smul c (nativePoissonExteriorCurve P (T F) t))
    filter_upwards [boundaryJoint_ae P T F t,hc] with θ hF hc
    change w (t,θ)=_ at hF
    rw [hF]
    simpa only [Pi.smul_apply,smul_eq_mul] using (hc (mem_univ θ)).symm
  have h := nativePoissonExteriorCollarValue_eq_lift P (T (c•F)) (hT (c•F))
    (measurable_const.mul (boundaryJoint_measurable P T F)) hae
  change (nativePoissonExteriorCollarValue P (T (c•F)) : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
    cylinderLift (fun p => c*w p) at h
  rw [native_cylinderLift_smul] at h
  apply Lp.ext
  filter_upwards [h,Lp.coeFn_smul c (nativePoissonExteriorCollarValue P (T F)),
    nativePoissonExteriorCollarValue_eq_lift P (T F) (hT F) (boundaryJoint_measurable P T F) (boundaryJoint_ae P T F)] with x hx hc hF
  rw [hx,hc]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hF]

#print axioms nativeExteriorBoundaryValue_add
#print axioms nativeExteriorBoundaryValue_smul
end Yamabe3.Analysis.SpherePolar
