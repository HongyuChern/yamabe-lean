import Yamabe3.Analysis.NativeCollarSeriesIdentification

/-! Physical collar lifts depend only on the genuine continuous angular
curve, not on the jointly measurable representative. No sphere restriction
of a volume almost-everywhere equality is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeEntranceCollar_subset_shell :
    nativePoissonEntranceCollar ⊆ cylinderShell (-(1/2:ℝ)) (1/2) := by
  intro x hx
  have h := (nativePolarTimeWindow_norm (1/2) x).mp hx
  exact ⟨h.1.le,by simpa only [neg_neg] using h.2.le⟩

theorem native_shell_lift_ae_eq_of_joint_slices
    {w z : ℝ × S → ℝ} (hw : Measurable w) (hz : Measurable z)
    (hae : ∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume] (fun θ => z (t,θ))) (a b : ℝ) :
    cylinderLift w =ᵐ[volume.restrict (cylinderShell a b)] cylinderLift z := by
  have hzero (t : ℝ) : (fun θ => w (t,θ)-z (t,θ))=ᵐ[angularVolume]
      ((0 : AngularL2) : S → ℝ) := by
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp
      (Lp.coeFn_zero ℝ 2 (angularVolume.restrict univ))
    filter_upwards [hae t,hc] with θ hθ hc
    rw [hθ,sub_self]
    exact (hc (mem_univ θ)).symm
  have hm := memLp_continuous_angular_lift (continuous_const : Continuous (fun _ : ℝ => (0 : AngularL2)))
    (hw.sub hz) hzero a b
  have hi := integral_cylinderLift_sq_shell_eq (continuous_const : Continuous (fun _ : ℝ => (0 : AngularL2)))
    (hw.sub hz) hzero a b
  change (∫ x in cylinderShell a b,cylinderLift (fun p => w p-z p) x^2)=_ at hi
  have hzint : (∫ x in cylinderShell a b,cylinderLift (fun p => w p-z p) x^2)=0 := by simpa using hi
  have hs := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg
    (cylinderLift (fun p => w p-z p) x)) hm.integrable_sq).mp hzint
  rw [cylinderLift_sub] at hs
  filter_upwards [hs] with x hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)

theorem native_collar_lift_ae_eq_of_joint_slices
    {w z : ℝ × S → ℝ} (hw : Measurable w) (hz : Measurable z)
    (hae : ∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume] (fun θ => z (t,θ))) :
    cylinderLift w =ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift z :=
  ae_mono (Measure.restrict_mono nativeEntranceCollar_subset_shell le_rfl)
    (native_shell_lift_ae_eq_of_joint_slices hw hz hae _ _)

theorem native_collar_lift_memLp {U : ℝ → AngularL2} (hU : Continuous U)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume] (U t : S → ℝ)) :
    MemLp (cylinderLift w) 2 (volume.restrict nativePoissonEntranceCollar) :=
  (memLp_continuous_angular_lift hU hw hae _ _).mono_measure
    (Measure.restrict_mono nativeEntranceCollar_subset_shell le_rfl)

theorem native_cylinderLift_add (w z : ℝ × S → ℝ) :
    cylinderLift (fun p => w p+z p)=fun x => cylinderLift w x+cylinderLift z x := by
  funext x
  by_cases hx : x=0
  · subst x
    simp only [cylinderLift_zero,add_zero]
  · let y : puncturedSpace := ⟨x,by change x≠0;exact hx⟩
    change cylinderLift (fun p => w p+z p) (y:E)=cylinderLift w (y:E)+cylinderLift z (y:E)
    simp only [cylinderLift_coe,puncturedCylinderLift,mul_add]

theorem native_cylinderLift_smul (c : ℝ) (w : ℝ × S → ℝ) :
    cylinderLift (fun p => c*w p)=fun x => c*cylinderLift w x := by
  funext x
  by_cases hx : x=0
  · subst x
    simp only [cylinderLift_zero,mul_zero]
  · let y : puncturedSpace := ⟨x,by change x≠0;exact hx⟩
    change cylinderLift (fun p => c*w p) (y:E)=c*cylinderLift w (y:E)
    simp only [cylinderLift_coe,puncturedCylinderLift]
    ring

#print axioms native_shell_lift_ae_eq_of_joint_slices
#print axioms native_collar_lift_ae_eq_of_joint_slices
#print axioms native_collar_lift_memLp
#print axioms native_cylinderLift_add
#print axioms native_cylinderLift_smul
end Yamabe3.Analysis.SpherePolar
