import Yamabe3.Analysis.NativeL2HalfAllScaleIdentity

/-! Actual bounded linear value and weak-jet maps, uniform over all
collar scales, for the same source and fixed entrance correction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic
variable (P : NativeHighPotential)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
  (s : ℝ)

private def halfJoint (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) : ℝ × S → ℝ :=
  (exists_joint_L2_representative_of_continuous (nativeL2HalfCollarCurve_continuous P hplus F)).choose
private theorem halfJoint_measurable (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    Measurable (halfJoint P hplus F) :=
  (exists_joint_L2_representative_of_continuous (nativeL2HalfCollarCurve_continuous P hplus F)).choose_spec.1.measurable
private theorem halfJoint_ae (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) (t : ℝ) :
    (fun θ => halfJoint P hplus F (t,θ))=ᵐ[angularVolume] (nativeL2HalfCollarCurve P hplus F t : S → ℝ) := by
  simpa only [halfJoint,Measure.restrict_univ] using
    (exists_joint_L2_representative_of_continuous (nativeL2HalfCollarCurve_continuous P hplus F)).choose_spec.2 t

theorem nativeL2HalfAllScaleValue_add (F G : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeL2HalfAllScaleValue P hplus s (F+G)=nativeL2HalfAllScaleValue P hplus s F+nativeL2HalfAllScaleValue P hplus s G := by
  let w := halfJoint P hplus F
  let z := halfJoint P hplus G
  have hae (t : ℝ) : (fun θ => w (t,θ)+z (t,θ))=ᵐ[angularVolume]
      (nativeL2HalfCollarCurve P hplus (F+G) t : S → ℝ) := by
    rw [nativeL2HalfCollarCurve_add]
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp
      (Lp.coeFn_add (nativeL2HalfCollarCurve P hplus F t) (nativeL2HalfCollarCurve P hplus G t))
    filter_upwards [halfJoint_ae P hplus F t,halfJoint_ae P hplus G t,hc] with θ hF hG hc
    change w (t,θ)=_ at hF
    change z (t,θ)=_ at hG
    rw [hF,hG]
    exact (hc (mem_univ θ)).symm
  have h := nativeL2HalfAllScaleValue_same_field P hplus (F+G)
    ((halfJoint_measurable P hplus F).add (halfJoint_measurable P hplus G)) hae s
  change (nativeL2HalfAllScaleValue P hplus s (F+G) : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
    (fun x => Real.exp (3*s/2)*cylinderLift (fun p => w p+z p) (Real.exp (-s) • x)) at h
  rw [native_cylinderLift_add] at h
  apply Lp.ext
  filter_upwards [h,Lp.coeFn_add (nativeL2HalfAllScaleValue P hplus s F) (nativeL2HalfAllScaleValue P hplus s G),
    nativeL2HalfAllScaleValue_same_field P hplus F (halfJoint_measurable P hplus F) (halfJoint_ae P hplus F) s,
    nativeL2HalfAllScaleValue_same_field P hplus G (halfJoint_measurable P hplus G) (halfJoint_ae P hplus G) s] with x hx hc hF hG
  rw [hx,hc]
  simp only [Pi.add_apply]
  rw [hF,hG]
  ring

theorem nativeL2HalfAllScaleValue_smul (c : ℝ) (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeL2HalfAllScaleValue P hplus s (c•F)=c•nativeL2HalfAllScaleValue P hplus s F := by
  let w := halfJoint P hplus F
  have hae (t : ℝ) : (fun θ => c*w (t,θ))=ᵐ[angularVolume]
      (nativeL2HalfCollarCurve P hplus (c•F) t : S → ℝ) := by
    rw [nativeL2HalfCollarCurve_smul]
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp (Lp.coeFn_smul c (nativeL2HalfCollarCurve P hplus F t))
    filter_upwards [halfJoint_ae P hplus F t,hc] with θ hF hc
    change w (t,θ)=_ at hF
    rw [hF]
    simpa only [Pi.smul_apply,smul_eq_mul] using (hc (mem_univ θ)).symm
  have h := nativeL2HalfAllScaleValue_same_field P hplus (c•F)
    (measurable_const.mul (halfJoint_measurable P hplus F)) hae s
  change (nativeL2HalfAllScaleValue P hplus s (c•F) : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
    (fun x => Real.exp (3*s/2)*cylinderLift (fun p => c*w p) (Real.exp (-s) • x)) at h
  rw [native_cylinderLift_smul] at h
  apply Lp.ext
  filter_upwards [h,Lp.coeFn_smul c (nativeL2HalfAllScaleValue P hplus s F),
    nativeL2HalfAllScaleValue_same_field P hplus F (halfJoint_measurable P hplus F) (halfJoint_ae P hplus F) s] with x hx hc hF
  rw [hx,hc]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hF]
  ring

def nativeL2HalfAllScaleValueLinear :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →ₗ[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) where
  toFun := nativeL2HalfAllScaleValue P hplus s
  map_add' := nativeL2HalfAllScaleValue_add P hplus s
  map_smul' := nativeL2HalfAllScaleValue_smul P hplus s

def nativeL2HalfAllScaleFirstLinear (j : Fin 3) :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →ₗ[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeL2WeakDerivativeLinearMap (nativePolarTimeWindow_open (1/2)) j (nativeL2HalfAllScaleValueLinear P hplus s)
    (fun F => nativeL2HalfAllScaleFirst P hplus s F j) (fun F => (nativeL2HalfAllScale_H2_same_jets P hplus s F).2.1 j)

def nativeL2HalfAllScaleSecondLinear (k j : Fin 3) :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →ₗ[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeL2WeakDerivativeLinearMap (nativePolarTimeWindow_open (1/2)) k (nativeL2HalfAllScaleFirstLinear P hplus s j)
    (fun F => nativeL2HalfAllScaleSecond P hplus s F k j) (fun F => (nativeL2HalfAllScale_H2_same_jets P hplus s F).2.2 k j)

def nativeL2HalfAllScaleValueCLM :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  (nativeL2HalfAllScaleValueLinear P hplus s).mkContinuousOfExistsBound (by
    obtain ⟨C,G,K,_,_,_,h⟩ := exists_nativeL2HalfAllScale_uniform_H2_bounds P hplus
    exact ⟨C,fun F => (h F s).1⟩)

def nativeL2HalfAllScaleFirstCLM (j : Fin 3) :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  (nativeL2HalfAllScaleFirstLinear P hplus s j).mkContinuousOfExistsBound (by
    obtain ⟨C,G,K,_,_,_,h⟩ := exists_nativeL2HalfAllScale_uniform_H2_bounds P hplus
    exact ⟨G,fun F => (h F s).2.1 j⟩)

def nativeL2HalfAllScaleSecondCLM (k j : Fin 3) :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  (nativeL2HalfAllScaleSecondLinear P hplus s k j).mkContinuousOfExistsBound (by
    obtain ⟨C,G,K,_,_,_,h⟩ := exists_nativeL2HalfAllScale_uniform_H2_bounds P hplus
    exact ⟨K k,fun F => (h F s).2.2 k j⟩)

omit s in
 theorem exists_nativeL2HalfAllScale_operator_bounds :
    ∃ (C G : ℝ) (K : Fin 3 → ℝ),0 ≤ C ∧ 0 ≤ G ∧ (∀ k,0 ≤ K k) ∧
      ∀ s : ℝ, ‖nativeL2HalfAllScaleValueCLM P hplus s‖ ≤ C ∧
        (∀ j,‖nativeL2HalfAllScaleFirstCLM P hplus s j‖ ≤ G) ∧
        (∀ k j,‖nativeL2HalfAllScaleSecondCLM P hplus s k j‖ ≤ K k) := by
  obtain ⟨C,G,K,hC,hG,hK,h⟩ := exists_nativeL2HalfAllScale_uniform_H2_bounds P hplus
  exact ⟨C,G,K,hC,hG,hK,fun s => ⟨ContinuousLinearMap.opNorm_le_bound _ hC (fun F => (h F s).1),
    fun j => ContinuousLinearMap.opNorm_le_bound _ hG (fun F => (h F s).2.1 j),
    fun k j => ContinuousLinearMap.opNorm_le_bound _ (hK k) (fun F => (h F s).2.2 k j)⟩⟩

#print axioms nativeL2HalfAllScaleValue_add
#print axioms nativeL2HalfAllScaleValue_smul
#print axioms nativeL2HalfAllScaleValueCLM
#print axioms nativeL2HalfAllScaleFirstCLM
#print axioms nativeL2HalfAllScaleSecondCLM
#print axioms exists_nativeL2HalfAllScale_operator_bounds
end Yamabe3.Analysis.SpherePolar
