import Yamabe3.Analysis.NativePhysicalPairTestScaling
import Yamabe3.Analysis.NativePhysicalSourceDuality
import Yamabe3.Analysis.NativeCollarPotentialMultiplier

/-! A bounded source return from the entire physical collar. Its exact
physical test pairing is proved with the Euclidean volume Jacobian and
the inverse-square weight. The adjoint alone is not called a right
inverse; reconstruction is proved separately from these pairings. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeFullCollarSourceReturnCLM : NativeCollarL2 →L[ℝ] Lp AngularSpectralSpace 2 (volume : Measure ℝ) :=
  (ContinuousLinearMap.adjoint nativeL2FullPhysicalSourceCLM).comp
    (nativeCollarPotentialMulCLM (BoundedContinuousFunction.const ℝ (1:ℝ)))

theorem nativeL2FullPhysicalSource_representation (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    (nativeL2FullPhysicalSourceCLM F : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      nativeFullPhysicalSourceRepresentative F :=
  nativeL2CollarLift_eq_lift (nativeL2FullAngularCLM F)
    (nativeAngularL2Joint_measurable _) (Eventually.of_forall (nativeAngularL2Joint_ae _))

variable (φ : E→ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (h0 : (0:E)∉tsupport φ)

theorem nativePhysicalPairTestL2_collar_lift :
    (nativeL2FullPhysicalSourceCLM (nativePhysicalPairTestL2 φ hφ hc h0) : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => ‖x‖^2*φ x) := by
  let F := nativePhysicalPairTestL2 φ hφ hc h0
  have hz : l2TimeTranslateCLM AngularSpectralSpace 0 F=F := by
    apply Lp.ext
    simpa only [add_zero] using l2TimeTranslate_ae AngularSpectralSpace 0 F
  have h := nativePhysicalPairTestL2_shift_lift φ hφ hc h0 0
  change (nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace 0 F) : E→ℝ)=ᵐ[_] _ at h
  rw [hz] at h
  filter_upwards [h,ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hx hxc
  rw [hx]
  have he := nativePhysicalPairTest_scaling φ 0 (cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hxc))
  simpa only [add_zero,mul_zero,zero_div,neg_zero,Real.exp_zero,mul_one,one_smul] using he

theorem nativeFullCollarSourceReturn_physical_test (U : NativeCollarL2) :
    inner ℝ (nativeFullCollarSourceReturnCLM U) (nativePhysicalPairTestL2 φ hφ hc h0)=
      ∫x in nativePoissonEntranceCollar,U x*φ x := by
  let V := BoundedContinuousFunction.const ℝ (1:ℝ)
  change inner ℝ ((ContinuousLinearMap.adjoint nativeL2FullPhysicalSourceCLM)
    (nativeCollarPotentialMulCLM V U)) (nativePhysicalPairTestL2 φ hφ hc h0)=_
  rw [ContinuousLinearMap.adjoint_inner_left,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [nativeCollarPotentialMulCLM_ae V U,nativePhysicalPairTestL2_collar_lift φ hφ hc h0,
    ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hm ht hx
  simp only [RCLike.inner_apply,conj_trivial,hm,ht]
  change (‖x‖^2*φ x)*((1/‖x‖^2)*U x)=U x*φ x
  have hn : ‖x‖≠0 := norm_ne_zero_iff.mpr (cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx))
  field_simp

theorem nativeL2FullPhysicalSource_physical_test_on_collar
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (hs : tsupport φ⊆nativePoissonEntranceCollar) :
    inner ℝ F (nativePhysicalPairTestL2 φ hφ hc h0)=
      ∫x in nativePoissonEntranceCollar,(nativeL2FullPhysicalSourceCLM F : E→ℝ) x*φ x := by
  obtain ⟨hi,he⟩ := nativeFullPhysicalSource_physical_test_pairing F φ hφ hc h0
  have hr : (∫x : E,nativeFullPhysicalSourceRepresentative F x*φ x)=
      ∫x in nativePoissonEntranceCollar,nativeFullPhysicalSourceRepresentative F x*φ x := by
    have hO : MeasurableSet nativePoissonEntranceCollar := (nativePolarTimeWindow_open (1/2)).measurableSet
    rw [←integral_indicator hO]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x∈nativePoissonEntranceCollar
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx]
      change nativeFullPhysicalSourceRepresentative F x*φ x=0
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)),mul_zero]
  apply he.trans (hr.trans ?_)
  apply integral_congr_ae
  filter_upwards [nativeL2FullPhysicalSource_representation F] with x hx
  rw [hx]

#print axioms nativeL2FullPhysicalSource_representation
#print axioms nativePhysicalPairTestL2_collar_lift
#print axioms nativeFullCollarSourceReturn_physical_test
#print axioms nativeL2FullPhysicalSource_physical_test_on_collar
end Yamabe3.Analysis.SpherePolar
