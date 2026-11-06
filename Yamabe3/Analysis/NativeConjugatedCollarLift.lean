import Yamabe3.Analysis.NativeCollarLiftRepresentative

/-! A bounded physical collar lift of an actual bounded continuous
angular curve, with the physical time factor exp(-2t). The factor is only
bounded on the fixed collar, never on the entire real line. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

def nativeConjugatedCurve (W : ℝ →ᵇ AngularL2) (t : ℝ) : AngularL2 := Real.exp (-2*t) • W t

theorem nativeConjugatedCurve_continuous (W : ℝ →ᵇ AngularL2) : Continuous (nativeConjugatedCurve W) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul W.continuous

def nativeConjugatedJoint (W : ℝ →ᵇ AngularL2) : ℝ × S → ℝ :=
  Classical.choose (exists_joint_L2_representative_of_continuous (nativeConjugatedCurve_continuous W))

theorem nativeConjugatedJoint_measurable (W : ℝ →ᵇ AngularL2) : Measurable (nativeConjugatedJoint W) :=
  (Classical.choose_spec (exists_joint_L2_representative_of_continuous (nativeConjugatedCurve_continuous W))).1.measurable

theorem nativeConjugatedJoint_ae (W : ℝ →ᵇ AngularL2) (t : ℝ) :
    (fun θ => nativeConjugatedJoint W (t,θ))=ᵐ[angularVolume] (nativeConjugatedCurve W t : S → ℝ) := by
  simpa only [nativeConjugatedJoint,Measure.restrict_univ] using
    (Classical.choose_spec (exists_joint_L2_representative_of_continuous (nativeConjugatedCurve_continuous W))).2 t

def nativeConjugatedCollarLp (W : ℝ →ᵇ AngularL2) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  (native_collar_lift_memLp (nativeConjugatedCurve_continuous W) (nativeConjugatedJoint_measurable W)
    (nativeConjugatedJoint_ae W)).toLp (cylinderLift (nativeConjugatedJoint W))

theorem nativeConjugatedCollarLp_eq_lift (W : ℝ →ᵇ AngularL2)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume] (nativeConjugatedCurve W t : S → ℝ)) :
    (nativeConjugatedCollarLp W : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w :=
  (native_collar_lift_memLp (nativeConjugatedCurve_continuous W) (nativeConjugatedJoint_measurable W)
    (nativeConjugatedJoint_ae W)).coeFn_toLp.trans
      (native_collar_lift_ae_eq_of_joint_slices (nativeConjugatedJoint_measurable W) hw
        (fun t => (nativeConjugatedJoint_ae W t).trans (hae t).symm))

theorem nativeConjugatedCollarLp_norm_le (W : ℝ →ᵇ AngularL2) :
    ‖nativeConjugatedCollarLp W‖ ≤ Real.sqrt (Real.exp 1*Real.exp 2)*‖W‖ := by
  let w := nativeConjugatedJoint W
  have hU := nativeConjugatedCurve_continuous W
  have hw := nativeConjugatedJoint_measurable W
  have hae := nativeConjugatedJoint_ae W
  have hm := memLp_continuous_angular_lift hU hw hae (-(1/2:ℝ)) (1/2)
  have hsub := setIntegral_mono_set (s := nativePoissonEntranceCollar) hm.integrable_sq
    (Eventually.of_forall fun x => sq_nonneg (cylinderLift w x))
    (Eventually.of_forall fun x hx => nativeEntranceCollar_subset_shell hx)
  have hb := integral_cylinderLift_sq_shell_le hU hw hae (-(1/2:ℝ)) (1/2)
  have ht : (∫ t : ℝ in Icc (-(1/2:ℝ)) (1/2),‖nativeConjugatedCurve W t‖^2) ≤
      Real.exp 2*‖W‖^2 := by
    have he (t : ℝ) (ht : t ∈ Icc (-(1/2:ℝ)) (1/2)) :
        ‖nativeConjugatedCurve W t‖^2 ≤ Real.exp 2*‖W‖^2 := by
      have hx : Real.exp (-2*t) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith [ht.1])
      have hn : ‖W t‖ ≤ ‖W‖ := W.norm_coe_le_norm t
      rw [nativeConjugatedCurve,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,mul_pow]
      have he2 : Real.exp 1^2=Real.exp 2 := by rw [pow_two,←Real.exp_add];norm_num
      rw [←he2]
      exact mul_le_mul (sq_le_sq₀ (Real.exp_pos _).le (Real.exp_pos _).le |>.2 hx)
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2 hn) (sq_nonneg _) (sq_nonneg _)
    have hi := setIntegral_mono_on (μ := (volume : Measure ℝ)) (hU.norm.pow 2).integrableOn_Icc
      ((continuous_const : Continuous (fun _ : ℝ => Real.exp 2*‖W‖^2)).integrableOn_Icc) measurableSet_Icc he
    norm_num [integral_const,Real.volume_Icc] at hi ⊢
    exact hi
  have hn := native_norm_toLp_sq_eq_integral_sq
    (native_collar_lift_memLp hU hw hae)
  change ‖nativeConjugatedCollarLp W‖^2=_ at hn
  have hh : ‖nativeConjugatedCollarLp W‖^2 ≤ (Real.exp 1*Real.exp 2)*‖W‖^2 := by
    rw [hn]
    have h := hsub.trans (hb.trans (mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le))
    norm_num at h
    simpa only [mul_assoc] using h
  have hs := Real.sq_sqrt (show 0 ≤ Real.exp 1*Real.exp 2 by positivity)
  have hpos : 0 ≤ Real.sqrt (Real.exp 1*Real.exp 2)*‖W‖ := by positivity
  nlinarith [norm_nonneg (nativeConjugatedCollarLp W),sq_nonneg
    (‖nativeConjugatedCollarLp W‖-Real.sqrt (Real.exp 1*Real.exp 2)*‖W‖)]

theorem nativeConjugatedCollarLp_add (W Z : ℝ →ᵇ AngularL2) :
    nativeConjugatedCollarLp (W+Z)=nativeConjugatedCollarLp W+nativeConjugatedCollarLp Z := by
  let w := nativeConjugatedJoint W
  let z := nativeConjugatedJoint Z
  have hae (t : ℝ) : (fun θ => w (t,θ)+z (t,θ))=ᵐ[angularVolume]
      (nativeConjugatedCurve (W+Z) t : S → ℝ) := by
    have he : nativeConjugatedCurve (W+Z) t=nativeConjugatedCurve W t+nativeConjugatedCurve Z t := by
      simp only [nativeConjugatedCurve,BoundedContinuousFunction.add_apply,smul_add]
    rw [he]
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp
      (Lp.coeFn_add (nativeConjugatedCurve W t) (nativeConjugatedCurve Z t))
    filter_upwards [nativeConjugatedJoint_ae W t,nativeConjugatedJoint_ae Z t,hc] with θ hW hZ hc
    change w (t,θ)+z (t,θ)=_
    rw [show w (t,θ)=_ from hW,show z (t,θ)=_ from hZ]
    exact (hc (mem_univ θ)).symm
  have h := nativeConjugatedCollarLp_eq_lift (W+Z)
    ((nativeConjugatedJoint_measurable W).add (nativeConjugatedJoint_measurable Z)) hae
  change (nativeConjugatedCollarLp (W+Z) : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift (fun p => w p+z p) at h
  rw [native_cylinderLift_add] at h
  apply Lp.ext
  filter_upwards [h,Lp.coeFn_add (nativeConjugatedCollarLp W) (nativeConjugatedCollarLp Z),
    nativeConjugatedCollarLp_eq_lift W (nativeConjugatedJoint_measurable W) (nativeConjugatedJoint_ae W),
    nativeConjugatedCollarLp_eq_lift Z (nativeConjugatedJoint_measurable Z) (nativeConjugatedJoint_ae Z)] with x hx hc hW hZ
  change (nativeConjugatedCollarLp (W+Z)) x= _
  rw [hx,hc]
  change cylinderLift w x+cylinderLift z x=nativeConjugatedCollarLp W x+nativeConjugatedCollarLp Z x
  rw [hW,hZ]

theorem nativeConjugatedCollarLp_smul (c : ℝ) (W : ℝ →ᵇ AngularL2) :
    nativeConjugatedCollarLp (c•W)=c•nativeConjugatedCollarLp W := by
  let w := nativeConjugatedJoint W
  have hae (t : ℝ) : (fun θ => c*w (t,θ))=ᵐ[angularVolume]
      (nativeConjugatedCurve (c•W) t : S → ℝ) := by
    have he : nativeConjugatedCurve (c•W) t=c•nativeConjugatedCurve W t := by
      simp only [nativeConjugatedCurve,BoundedContinuousFunction.smul_apply,smul_comm (Real.exp (-2*t)) c]
    rw [he]
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp (Lp.coeFn_smul c (nativeConjugatedCurve W t))
    filter_upwards [nativeConjugatedJoint_ae W t,hc] with θ hW hc
    change c*w (t,θ)=_
    rw [show w (t,θ)=_ from hW]
    simpa only [Pi.smul_apply,smul_eq_mul] using (hc (mem_univ θ)).symm
  have h := nativeConjugatedCollarLp_eq_lift (c•W)
    (measurable_const.mul (nativeConjugatedJoint_measurable W)) hae
  change (nativeConjugatedCollarLp (c•W) : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift (fun p => c*w p) at h
  rw [native_cylinderLift_smul] at h
  apply Lp.ext
  filter_upwards [h,Lp.coeFn_smul c (nativeConjugatedCollarLp W),
    nativeConjugatedCollarLp_eq_lift W (nativeConjugatedJoint_measurable W) (nativeConjugatedJoint_ae W)] with x hx hc hW
  rw [hx,hc]
  change c*cylinderLift w x=c*nativeConjugatedCollarLp W x
  rw [hW]

def nativeConjugatedCollarCLM : (ℝ →ᵇ AngularL2) →L[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ({toFun := nativeConjugatedCollarLp
    map_add' := nativeConjugatedCollarLp_add
    map_smul' := nativeConjugatedCollarLp_smul} :
    (ℝ →ᵇ AngularL2) →ₗ[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar)).mkContinuous
      (Real.sqrt (Real.exp 1*Real.exp 2)) nativeConjugatedCollarLp_norm_le

#print axioms nativeConjugatedCollarLp_eq_lift
#print axioms nativeConjugatedCollarLp_norm_le
#print axioms nativeConjugatedCollarLp_add
#print axioms nativeConjugatedCollarLp_smul
#print axioms nativeConjugatedCollarCLM
end Yamabe3.Analysis.SpherePolar
