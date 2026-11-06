import Yamabe3.Analysis.NativePhysicalPairTest

/-! The exact physical pairing weight: the spectral test lift cancels
|x|^-2 and leaves exp(-5s/2), which combines with the Jacobian row scaling
to give the three-dimensional volume dilation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativePhysicalPairTest_scaling (φ : E → ℝ) (s : ℝ) {x : E} (hx : x≠0) :
    cylinderLift (fun p => nativePhysicalPairTestPullback φ (p.1+s,p.2)) x=
      ‖x‖^2*Real.exp (-5*s/2)*φ (Real.exp (-s) • x) := by
  let y : puncturedSpace := ⟨x,by change x≠0;exact hx⟩
  let p := cylinderCoordinates y
  have hpoint : cylinderPoint p=x := cylinderPoint_coordinates y
  rw [←hpoint]
  change cylinderLift (fun p => nativePhysicalPairTestPullback φ (p.1+s,p.2))
    (Real.exp (-p.1) • (p.2:E))=_
  rw [cylinderLift_smul _ (Real.exp_pos _) p.2,Real.log_exp,neg_neg,radialScale_exp_neg]
  change Real.exp (p.1/2)*(Real.exp (-2*(p.1+s))*(Real.exp (-(p.1+s)/2)*φ (cylinderPoint (p.1+s,p.2))))=_
  have hshift : cylinderPoint (p.1+s,p.2)=Real.exp (-s) • cylinderPoint p := by
    simp only [cylinderPoint,smul_smul]
    rw [←Real.exp_add]
    congr 2
    ring
  rw [hshift,cylinderPoint_norm]
  have he : Real.exp (p.1/2)*Real.exp (-2*(p.1+s))*Real.exp (-(p.1+s)/2)=
      Real.exp (-p.1)^2*Real.exp (-5*s/2) := by
    rw [←Real.exp_add,←Real.exp_add,←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    ring
  calc
    _=(Real.exp (p.1/2)*Real.exp (-2*(p.1+s))*Real.exp (-(p.1+s)/2))*φ (Real.exp (-s) • cylinderPoint p) := by ring
    _=_ := by rw [he]

theorem nativePhysicalPairTest_weight_cancel (φ : E → ℝ) (s : ℝ) (U : E → ℝ) (x : E) :
    nativeShellSourceWeight x*U x*cylinderLift (fun p => nativePhysicalPairTestPullback φ (p.1+s,p.2)) x=
      nativeSourceShell.indicator (fun x => Real.exp (-5*s/2)*(U x*φ (Real.exp (-s) • x))) x := by
  by_cases hx : x∈nativeSourceShell
  · rw [indicator_of_mem hx,nativePhysicalPairTest_scaling φ s hx.1,
      nativeShellSourceWeight,indicator_of_mem hx]
    simp only [nativeHalfEndPotentialCoefficient,BoundedContinuousFunction.const_apply]
    have hn : ‖x‖≠0 := norm_ne_zero_iff.mpr hx.1
    field_simp
  · simp only [nativeShellSourceWeight,indicator_of_notMem hx,zero_mul]

variable (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (h0 : (0:E)∉tsupport φ)

theorem nativeFullShellSourceReturn_physical_test (s : ℝ) (U : NativeCollarL2) :
    inner ℝ (nativeFullShellSourceReturnCLM s U) (nativePhysicalPairTestL2 φ hφ hc h0)=
      Real.exp (-5*s/2)*(∫ x in nativeSourceShell,U x*φ (Real.exp (-s) • x)) := by
  rw [nativeFullShellSourceReturn_pairing]
  calc
    _=∫x in nativePoissonEntranceCollar,nativeSourceShell.indicator
      (fun x => Real.exp (-5*s/2)*(U x*φ (Real.exp (-s) • x))) x := by
      apply integral_congr_ae
      filter_upwards [nativePhysicalPairTestL2_shift_lift φ hφ hc h0 s] with x hx
      rw [hx]
      exact nativePhysicalPairTest_weight_cancel φ s U x
    _=∫x in nativeSourceShell,Real.exp (-5*s/2)*(U x*φ (Real.exp (-s) • x)) := by
      rw [setIntegral_indicator nativeSourceShell_measurable]
      rw [inter_eq_right.mpr nativeSourceShell_subset_collar]
    _=_ := integral_const_mul _ _

#print axioms nativePhysicalPairTest_scaling
#print axioms nativePhysicalPairTest_weight_cancel
#print axioms nativeFullShellSourceReturn_physical_test
end Yamabe3.Analysis.SpherePolar
