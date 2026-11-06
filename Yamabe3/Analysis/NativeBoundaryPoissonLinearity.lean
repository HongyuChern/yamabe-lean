import Yamabe3.Analysis.NativeFullBoundaryBudget
import Yamabe3.Analysis.NativeAllScaleJetClosure

/-! Linearity of the same physical Poisson field for a bounded linear
boundary producer. Actual weak jets are not supplied independently. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic
private theorem poisson_curve_add (P : NativeHighPotential) (a b : AngularH1) (t : ℝ) :
    P.curve (a+b) t=P.curve a t+P.curve b t := by
  change Real.exp (-2*t) • (nativeHalfHighPotentialPoissonCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg (a+b) t.toNNReal)=_
  rw [map_add,BoundedContinuousFunction.add_apply,smul_add]
  rfl
private theorem poisson_curve_smul (P : NativeHighPotential) (c : ℝ) (b : AngularH1) (t : ℝ) :
    P.curve (c•b) t=c•P.curve b t := by
  change Real.exp (-2*t) • (nativeHalfHighPotentialPoissonCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg (c•b) t.toNNReal)=_
  rw [map_smul,BoundedContinuousFunction.smul_apply,smul_comm (Real.exp (-2*t)) c]
  rfl
theorem nativePoissonReflectedCurve_add (P : NativeHighPotential) (a b : AngularH1) (t : ℝ) :
    nativePoissonReflectedCurve P (a+b) t=nativePoissonReflectedCurve P a t+nativePoissonReflectedCurve P b t := by
  unfold nativePoissonReflectedCurve
  split_ifs <;> simp only [poisson_curve_add,smul_add,Finset.sum_add_distrib]
theorem nativePoissonReflectedCurve_smul (P : NativeHighPotential) (c : ℝ) (b : AngularH1) (t : ℝ) :
    nativePoissonReflectedCurve P (c•b) t=c•nativePoissonReflectedCurve P b t := by
  unfold nativePoissonReflectedCurve
  split_ifs <;> simp only [poisson_curve_smul,smul_comm _ c,Finset.smul_sum]


variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable (P : NativeHighPotential)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
  (T : X →L[ℝ] AngularH1)
  (hT : ∀x,NativeAngularSpectralRegular (3/2) (angularEmbedding (T x)))
  (s : ℝ)

private def boundaryJoint (F : X) : ℝ × S → ℝ :=
  (exists_joint_L2_representative_of_continuous (nativePoissonReflectedCurve_continuous P (T F))).choose
private theorem boundaryJoint_measurable (F : X) :
    Measurable (boundaryJoint P T F) :=
  (exists_joint_L2_representative_of_continuous (nativePoissonReflectedCurve_continuous P (T F))).choose_spec.1.measurable
private theorem boundaryJoint_ae (F : X) (t : ℝ) :
    (fun θ => boundaryJoint P T F (t,θ))=ᵐ[angularVolume] (nativePoissonReflectedCurve P (T F) t : S → ℝ) := by
  simpa only [boundaryJoint,Measure.restrict_univ] using
    (exists_joint_L2_representative_of_continuous (nativePoissonReflectedCurve_continuous P (T F))).choose_spec.2 t

include hT in
theorem nativeBoundaryPoissonValue_add (F G : X) :
    nativePoissonAllScaleValue P hplus s (T (F+G))=nativePoissonAllScaleValue P hplus s (T F)+nativePoissonAllScaleValue P hplus s (T G) := by
  let w := boundaryJoint P T F
  let z := boundaryJoint P T G
  have hae (t : ℝ) : (fun θ => w (t,θ)+z (t,θ))=ᵐ[angularVolume]
      (nativePoissonReflectedCurve P (T (F+G)) t : S → ℝ) := by
    rw [map_add,nativePoissonReflectedCurve_add]
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp
      (Lp.coeFn_add (nativePoissonReflectedCurve P (T F) t) (nativePoissonReflectedCurve P (T G) t))
    filter_upwards [boundaryJoint_ae P T F t,boundaryJoint_ae P T G t,hc] with θ hF hG hc
    change w (t,θ)=_ at hF
    change z (t,θ)=_ at hG
    rw [hF,hG]
    exact (hc (mem_univ θ)).symm
  have h := nativePoissonAllScaleValue_same_field P hplus (T (F+G)) (hT (F+G))
    ((boundaryJoint_measurable P T F).add (boundaryJoint_measurable P T G)) hae s
  change (nativePoissonAllScaleValue P hplus s (T (F+G)) : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
    (fun x => Real.exp (3*s/2)*cylinderLift (fun p => w p+z p) (Real.exp (-s) • x)) at h
  rw [native_cylinderLift_add] at h
  apply Lp.ext
  filter_upwards [h,Lp.coeFn_add (nativePoissonAllScaleValue P hplus s (T F)) (nativePoissonAllScaleValue P hplus s (T G)),
    nativePoissonAllScaleValue_same_field P hplus (T F) (hT F) (boundaryJoint_measurable P T F) (boundaryJoint_ae P T F) s,
    nativePoissonAllScaleValue_same_field P hplus (T G) (hT G) (boundaryJoint_measurable P T G) (boundaryJoint_ae P T G) s] with x hx hc hF hG
  rw [hx,hc]
  simp only [Pi.add_apply]
  rw [hF,hG]
  ring

include hT in
theorem nativeBoundaryPoissonValue_smul (c : ℝ) (F : X) :
    nativePoissonAllScaleValue P hplus s (T (c•F))=c•nativePoissonAllScaleValue P hplus s (T F) := by
  let w := boundaryJoint P T F
  have hae (t : ℝ) : (fun θ => c*w (t,θ))=ᵐ[angularVolume]
      (nativePoissonReflectedCurve P (T (c•F)) t : S → ℝ) := by
    rw [map_smul,nativePoissonReflectedCurve_smul]
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp (Lp.coeFn_smul c (nativePoissonReflectedCurve P (T F) t))
    filter_upwards [boundaryJoint_ae P T F t,hc] with θ hF hc
    change w (t,θ)=_ at hF
    rw [hF]
    simpa only [Pi.smul_apply,smul_eq_mul] using (hc (mem_univ θ)).symm
  have h := nativePoissonAllScaleValue_same_field P hplus (T (c•F)) (hT (c•F))
    (measurable_const.mul (boundaryJoint_measurable P T F)) hae s
  change (nativePoissonAllScaleValue P hplus s (T (c•F)) : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
    (fun x => Real.exp (3*s/2)*cylinderLift (fun p => c*w p) (Real.exp (-s) • x)) at h
  rw [native_cylinderLift_smul] at h
  apply Lp.ext
  filter_upwards [h,Lp.coeFn_smul c (nativePoissonAllScaleValue P hplus s (T F)),
    nativePoissonAllScaleValue_same_field P hplus (T F) (hT F) (boundaryJoint_measurable P T F) (boundaryJoint_ae P T F) s] with x hx hc hF
  rw [hx,hc]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hF]
  ring

#print axioms nativePoissonReflectedCurve_add
#print axioms nativePoissonReflectedCurve_smul
#print axioms nativeBoundaryPoissonValue_add
#print axioms nativeBoundaryPoissonValue_smul
end Yamabe3.Analysis.SpherePolar
