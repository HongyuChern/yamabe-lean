import Yamabe3.Analysis.NativeL2HalfCollarBound

/-! Bounded linear source-to-H2 jets for the same actual zero-entrance
physical collar. Linearity of value classes uses same-curve representatives;
linearity of derivatives uses uniqueness, not new derivative inputs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
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
private theorem poisson_reflected_add (P : NativeHighPotential) (a b : AngularH1) (t : ℝ) :
    nativePoissonReflectedCurve P (a+b) t=nativePoissonReflectedCurve P a t+nativePoissonReflectedCurve P b t := by
  unfold nativePoissonReflectedCurve
  split_ifs <;> simp only [poisson_curve_add,smul_add,Finset.sum_add_distrib]
private theorem poisson_reflected_smul (P : NativeHighPotential) (c : ℝ) (b : AngularH1) (t : ℝ) :
    nativePoissonReflectedCurve P (c•b) t=c•nativePoissonReflectedCurve P b t := by
  unfold nativePoissonReflectedCurve
  split_ifs <;> simp only [poisson_curve_smul,smul_comm _ c,Finset.smul_sum]

variable (P : NativeHighPotential)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)

theorem nativeL2HalfCollarCurve_add (F G : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) (t : ℝ) :
    nativeL2HalfCollarCurve P hplus (F+G) t=nativeL2HalfCollarCurve P hplus F t+nativeL2HalfCollarCurve P hplus G t := by
  have he : nativeL2HalfEntrance P hplus (F+G)=nativeL2HalfEntrance P hplus F+nativeL2HalfEntrance P hplus G :=
    (nativeL2EntranceH1CLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus).map_add F G
  simp only [nativeL2HalfCollarCurve,nativeConjugatedCurve,map_add,BoundedContinuousFunction.add_apply,
    smul_add,he,poisson_reflected_add]
  abel

theorem nativeL2HalfCollarCurve_smul (c : ℝ) (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) (t : ℝ) :
    nativeL2HalfCollarCurve P hplus (c•F) t=c•nativeL2HalfCollarCurve P hplus F t := by
  have he : nativeL2HalfEntrance P hplus (c•F)=c•nativeL2HalfEntrance P hplus F :=
    (nativeL2EntranceH1CLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus).map_smul c F
  simp only [nativeL2HalfCollarCurve,nativeConjugatedCurve,map_smul,BoundedContinuousFunction.smul_apply,
    he,poisson_reflected_smul,smul_sub,smul_comm (Real.exp (-2*t)) c]

private def halfJoint (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) : ℝ × S → ℝ :=
  (exists_joint_L2_representative_of_continuous (nativeL2HalfCollarCurve_continuous P hplus F)).choose
private theorem halfJoint_measurable (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    Measurable (halfJoint P hplus F) :=
  (exists_joint_L2_representative_of_continuous (nativeL2HalfCollarCurve_continuous P hplus F)).choose_spec.1.measurable
private theorem halfJoint_ae (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) (t : ℝ) :
    (fun θ => halfJoint P hplus F (t,θ))=ᵐ[angularVolume] (nativeL2HalfCollarCurve P hplus F t : S → ℝ) := by
  simpa only [halfJoint,Measure.restrict_univ] using
    (exists_joint_L2_representative_of_continuous (nativeL2HalfCollarCurve_continuous P hplus F)).choose_spec.2 t

theorem nativeL2HalfCollarValue_add (F G : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeL2HalfCollarValue P hplus (F+G)=nativeL2HalfCollarValue P hplus F+nativeL2HalfCollarValue P hplus G := by
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
  have h := nativeL2HalfCollarValue_eq_lift P hplus (F+G)
    ((halfJoint_measurable P hplus F).add (halfJoint_measurable P hplus G)) hae
  change (nativeL2HalfCollarValue P hplus (F+G) : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
    cylinderLift (fun p => w p+z p) at h
  rw [native_cylinderLift_add] at h
  apply Lp.ext
  filter_upwards [h,Lp.coeFn_add (nativeL2HalfCollarValue P hplus F) (nativeL2HalfCollarValue P hplus G),
    nativeL2HalfCollarValue_eq_lift P hplus F (halfJoint_measurable P hplus F) (halfJoint_ae P hplus F),
    nativeL2HalfCollarValue_eq_lift P hplus G (halfJoint_measurable P hplus G) (halfJoint_ae P hplus G)] with x hx hc hF hG
  rw [hx,hc]
  simp only [Pi.add_apply]
  rw [hF,hG]

theorem nativeL2HalfCollarValue_smul (c : ℝ) (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeL2HalfCollarValue P hplus (c•F)=c•nativeL2HalfCollarValue P hplus F := by
  let w := halfJoint P hplus F
  have hae (t : ℝ) : (fun θ => c*w (t,θ))=ᵐ[angularVolume]
      (nativeL2HalfCollarCurve P hplus (c•F) t : S → ℝ) := by
    rw [nativeL2HalfCollarCurve_smul]
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp (Lp.coeFn_smul c (nativeL2HalfCollarCurve P hplus F t))
    filter_upwards [halfJoint_ae P hplus F t,hc] with θ hF hc
    change w (t,θ)=_ at hF
    rw [hF]
    simpa only [Pi.smul_apply,smul_eq_mul] using (hc (mem_univ θ)).symm
  have h := nativeL2HalfCollarValue_eq_lift P hplus (c•F)
    (measurable_const.mul (halfJoint_measurable P hplus F)) hae
  change (nativeL2HalfCollarValue P hplus (c•F) : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
    cylinderLift (fun p => c*w p) at h
  rw [native_cylinderLift_smul] at h
  apply Lp.ext
  filter_upwards [h,Lp.coeFn_smul c (nativeL2HalfCollarValue P hplus F),
    nativeL2HalfCollarValue_eq_lift P hplus F (halfJoint_measurable P hplus F) (halfJoint_ae P hplus F)] with x hx hc hF
  rw [hx,hc]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hF]

def nativeL2HalfCollarValueLinear :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →ₗ[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) where
  toFun := nativeL2HalfCollarValue P hplus
  map_add' := nativeL2HalfCollarValue_add P hplus
  map_smul' := nativeL2HalfCollarValue_smul P hplus

def nativeL2HalfCollarFirstLinear (j : Fin 3) :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →ₗ[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeL2WeakDerivativeLinearMap (nativePolarTimeWindow_open (1/2)) j (nativeL2HalfCollarValueLinear P hplus)
    (fun F => nativeL2HalfCollarFirst P hplus F j) (fun F => (nativeL2HalfCollar_H2_and_jets P hplus F).2.1 j)

def nativeL2HalfCollarSecondLinear (k j : Fin 3) :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →ₗ[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeL2WeakDerivativeLinearMap (nativePolarTimeWindow_open (1/2)) k (nativeL2HalfCollarFirstLinear P hplus j)
    (fun F => nativeL2HalfCollarSecond P hplus F k j) (fun F => (nativeL2HalfCollar_H2_and_jets P hplus F).2.2 k j)

#print axioms nativeL2HalfCollarCurve_add
#print axioms nativeL2HalfCollarCurve_smul
#print axioms nativeL2HalfCollarValue_add
#print axioms nativeL2HalfCollarValue_smul
#print axioms nativeL2HalfCollarValueLinear
#print axioms nativeL2HalfCollarFirstLinear
#print axioms nativeL2HalfCollarSecondLinear
end Yamabe3.Analysis.SpherePolar
