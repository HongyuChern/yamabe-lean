import Yamabe3.Analysis.NativeL2PolarTransport

/-! Actual bounded polar lift of an arbitrary L2 angular source. A genuine
joint representative is constructed from the strongly measurable Lp
representative. The physical class is independent of time/slice null sets. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

def nativeAngularL2Joint (F : Lp AngularL2 2 (volume : Measure ℝ)) : ℝ × S → ℝ :=
  (exists_joint_L2_representative (Lp.stronglyMeasurable F)).choose

theorem nativeAngularL2Joint_measurable (F : Lp AngularL2 2 (volume : Measure ℝ)) :
    Measurable (nativeAngularL2Joint F) :=
  (exists_joint_L2_representative (Lp.stronglyMeasurable F)).choose_spec.1.measurable

theorem nativeAngularL2Joint_ae (F : Lp AngularL2 2 (volume : Measure ℝ)) (t : ℝ) :
    (fun θ => nativeAngularL2Joint F (t,θ))=ᵐ[angularVolume] (F t : S → ℝ) := by
  simpa only [nativeAngularL2Joint,Measure.restrict_univ] using
    (exists_joint_L2_representative (Lp.stronglyMeasurable F)).choose_spec.2 t

theorem nativeL2_lift_memLp_collar {U : ℝ → AngularL2} (hU : MemLp U 2)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ᵐ t : ℝ ∂volume,(fun θ => w (t,θ))=ᵐ[angularVolume] (U t : S → ℝ)) :
    MemLp (cylinderLift w) 2 (volume.restrict nativePoissonEntranceCollar) :=
  (memLp_cylinderLift_on_shell hw _ _ (native_joint_memLp_interval_of_memLp hU hw hae _ _)).mono_measure
    (Measure.restrict_mono nativeEntranceCollar_subset_shell le_rfl)

def nativeL2CollarLift (F : Lp AngularL2 2 (volume : Measure ℝ)) : Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  (nativeL2_lift_memLp_collar (Lp.memLp F) (nativeAngularL2Joint_measurable F)
    (Eventually.of_forall (nativeAngularL2Joint_ae F))).toLp (cylinderLift (nativeAngularL2Joint F))

theorem nativeL2CollarLift_eq_lift (F : Lp AngularL2 2 (volume : Measure ℝ))
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ᵐ t : ℝ ∂volume,(fun θ => w (t,θ))=ᵐ[angularVolume] (F t : S → ℝ)) :
    (nativeL2CollarLift F : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w := by
  have h := native_shell_lift_ae_eq_of_ae_slices (nativeAngularL2Joint_measurable F) hw
    (by filter_upwards [hae] with t ht;exact (nativeAngularL2Joint_ae F t).trans ht.symm) (-(1/2:ℝ)) (1/2)
  exact (nativeL2_lift_memLp_collar (Lp.memLp F) (nativeAngularL2Joint_measurable F)
    (Eventually.of_forall (nativeAngularL2Joint_ae F))).coeFn_toLp.trans
      (ae_mono (Measure.restrict_mono nativeEntranceCollar_subset_shell le_rfl) h)

theorem nativeL2CollarLift_norm_le (F : Lp AngularL2 2 (volume : Measure ℝ)) :
    ‖nativeL2CollarLift F‖≤Real.sqrt (Real.exp 1)*‖F‖ := by
  let w := nativeAngularL2Joint F
  have hw := nativeAngularL2Joint_measurable F
  have hae : ∀ᵐ t : ℝ ∂volume,(fun θ => nativeAngularL2Joint F (t,θ))=ᵐ[angularVolume] (F t : S → ℝ) :=
    Eventually.of_forall (nativeAngularL2Joint_ae F)
  have hm := memLp_cylinderLift_on_shell hw (-(1/2:ℝ)) (1/2)
    (native_joint_memLp_interval_of_memLp (Lp.memLp F) hw hae _ _)
  have hsub := setIntegral_mono_set (s := nativePoissonEntranceCollar) hm.integrable_sq
    (Eventually.of_forall fun x => sq_nonneg (cylinderLift w x))
    (Eventually.of_forall fun x hx => nativeEntranceCollar_subset_shell hx)
  rw [native_L2_shell_square (Lp.memLp F) hw hae] at hsub
  have hF : Integrable (fun t : ℝ => ‖F t‖^2) := (memLp_two_iff_integrable_sq_norm (Lp.memLp F).1).mp (Lp.memLp F)
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-2*t)*‖F t‖^2) (Icc (-(1/2:ℝ)) (1/2)) := by
    apply hF.integrableOn.bdd_mul (c := Real.exp 1) (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le,Real.exp_le_exp]
    linarith [ht.1]
  have hb := integral_mono_ae hi (hF.integrableOn.const_mul (Real.exp 1)) (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [ht.1])) (sq_nonneg ‖F t‖))
  rw [integral_const_mul] at hb
  have hn : (∫ t : ℝ,‖F t‖^2)=‖F‖^2 := by
    rw [←real_inner_self_eq_norm_sq F,L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => (real_inner_self_eq_norm_sq (F t)).symm
  have hg := setIntegral_le_integral (s := Icc (-(1/2:ℝ)) (1/2)) hF
    (Eventually.of_forall fun t => sq_nonneg ‖F t‖)
  rw [hn] at hg
  have he := native_norm_toLp_sq_eq_integral_sq (nativeL2_lift_memLp_collar (Lp.memLp F) hw hae)
  change ‖nativeL2CollarLift F‖^2=_ at he
  have hh : ‖nativeL2CollarLift F‖^2≤Real.exp 1*‖F‖^2 := by
    rw [he]
    exact hsub.trans (hb.trans (mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le))
  have hs : (Real.sqrt (Real.exp 1)*‖F‖)^2=Real.exp 1*‖F‖^2 := by
    rw [mul_pow,Real.sq_sqrt (Real.exp_pos _).le]
  have hp : 0≤Real.sqrt (Real.exp 1)*‖F‖ := by positivity
  nlinarith [norm_nonneg (nativeL2CollarLift F)]

theorem nativeL2CollarLift_add (F G : Lp AngularL2 2 (volume : Measure ℝ)) :
    nativeL2CollarLift (F+G)=nativeL2CollarLift F+nativeL2CollarLift G := by
  let w := nativeAngularL2Joint F
  let z := nativeAngularL2Joint G
  have hae : ∀ᵐ t : ℝ ∂volume,(fun θ => w (t,θ)+z (t,θ))=ᵐ[angularVolume] ((F+G) t : S → ℝ) := by
    filter_upwards [Lp.coeFn_add F G] with t ht
    change (F+G) t=F t+G t at ht
    rw [ht]
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp (Lp.coeFn_add (F t) (G t))
    filter_upwards [nativeAngularL2Joint_ae F t,nativeAngularL2Joint_ae G t,hc] with θ hF hG hc
    change w (t,θ)=_ at hF
    change z (t,θ)=_ at hG
    rw [hF,hG]
    exact (hc (mem_univ θ)).symm
  have h := nativeL2CollarLift_eq_lift (F+G) ((nativeAngularL2Joint_measurable F).add (nativeAngularL2Joint_measurable G)) hae
  change (nativeL2CollarLift (F+G) : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift (fun p => w p+z p) at h
  rw [native_cylinderLift_add] at h
  apply Lp.ext
  filter_upwards [h,Lp.coeFn_add (nativeL2CollarLift F) (nativeL2CollarLift G),
    nativeL2CollarLift_eq_lift F (nativeAngularL2Joint_measurable F) (Eventually.of_forall (nativeAngularL2Joint_ae F)),
    nativeL2CollarLift_eq_lift G (nativeAngularL2Joint_measurable G) (Eventually.of_forall (nativeAngularL2Joint_ae G))] with x hx hc hF hG
  rw [hx,hc]
  simp only [Pi.add_apply]
  rw [hF,hG]

theorem nativeL2CollarLift_smul (c : ℝ) (F : Lp AngularL2 2 (volume : Measure ℝ)) :
    nativeL2CollarLift (c•F)=c•nativeL2CollarLift F := by
  let w := nativeAngularL2Joint F
  have hae : ∀ᵐ t : ℝ ∂volume,(fun θ => c*w (t,θ))=ᵐ[angularVolume] ((c•F) t : S → ℝ) := by
    filter_upwards [Lp.coeFn_smul c F] with t ht
    change (c•F) t=c•F t at ht
    rw [ht]
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp (Lp.coeFn_smul c (F t))
    filter_upwards [nativeAngularL2Joint_ae F t,hc] with θ hF hc
    change w (t,θ)=_ at hF
    rw [hF]
    simpa only [Pi.smul_apply,smul_eq_mul] using (hc (mem_univ θ)).symm
  have h := nativeL2CollarLift_eq_lift (c•F) (measurable_const.mul (nativeAngularL2Joint_measurable F)) hae
  change (nativeL2CollarLift (c•F) : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift (fun p => c*w p) at h
  rw [native_cylinderLift_smul] at h
  apply Lp.ext
  filter_upwards [h,Lp.coeFn_smul c (nativeL2CollarLift F),
    nativeL2CollarLift_eq_lift F (nativeAngularL2Joint_measurable F) (Eventually.of_forall (nativeAngularL2Joint_ae F))] with x hx hc hF
  rw [hx,hc]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hF]

def nativeL2CollarLiftCLM : Lp AngularL2 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ({toFun := nativeL2CollarLift
    map_add' := nativeL2CollarLift_add
    map_smul' := nativeL2CollarLift_smul} :
    Lp AngularL2 2 (volume : Measure ℝ) →ₗ[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar)).mkContinuous
      (Real.sqrt (Real.exp 1)) nativeL2CollarLift_norm_le

#print axioms nativeAngularL2Joint_measurable
#print axioms nativeAngularL2Joint_ae
#print axioms nativeL2CollarLift_eq_lift
#print axioms nativeL2CollarLift_norm_le
#print axioms nativeL2CollarLift_add
#print axioms nativeL2CollarLift_smul
#print axioms nativeL2CollarLiftCLM
end Yamabe3.Analysis.SpherePolar
