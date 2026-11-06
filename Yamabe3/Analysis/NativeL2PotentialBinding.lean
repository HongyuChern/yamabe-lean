import Yamabe3.Analysis.NativeCollarPotentialMultiplier
import Yamabe3.Analysis.NativeL2ParticularLaplacian
import Yamabe3.Analysis.NativeL2ParticularAllSourceIdentity

/-! The same spectral potential term is exactly the original physical
inverse-square coefficient times the same physical particular field.
This is a volume L2 identity; it does not prescribe sphere point values. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem native_cylinderLift_potential_weight (V : ℝ →ᵇ ℝ) (w : ℝ × S → ℝ) (x : E) :
    nativeHalfEndPotentialCoefficient V x*cylinderLift w x=
      cylinderLift (fun p => V p.1*(Real.exp (2*p.1)*w p)) x := by
  by_cases hx : x=0
  · subst x
    simp only [cylinderLift_zero,mul_zero]
  · let y : puncturedSpace := ⟨x,by change x≠0;exact hx⟩
    have hn : 0<‖x‖ := norm_pos_iff.mpr hx
    have he : Real.exp (2*(-Real.log ‖x‖))=(‖x‖^2)⁻¹ := by
      calc
        _=Real.exp (-(Real.log ‖x‖+Real.log ‖x‖)) := by congr 1;ring
        _=_ := by rw [Real.exp_neg,Real.exp_add,Real.exp_log hn,pow_two]
    change nativeHalfEndPotentialCoefficient V x*cylinderLift w (y:E)=
      cylinderLift (fun p => V p.1*(Real.exp (2*p.1)*w p)) (y:E)
    rw [cylinderLift_coe,cylinderLift_coe]
    change (V (-Real.log ‖x‖)/‖x‖^2)*(radialScale ‖x‖*w (cylinderCoordinates y))=
      radialScale ‖x‖*(V (-Real.log ‖x‖)*(Real.exp (2*(-Real.log ‖x‖))*w (cylinderCoordinates y)))
    rw [he]
    ring

variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
  (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|V (t-s)|)≤κ)

theorem nativeL2Particular_potential_binding
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeCollarPotentialMulCLM V (nativeL2ParticularValueCLM hκ0 hκ1 V hminus hplus F)=
      nativeL2HighPhysicalSourceCLM (spectralL2PotentialMulCLM V
        (spectralL2IntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
          (by norm_num : |(-2:ℝ)|<5/2) V F)) := by
  let U := spectralL2IntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
    (by norm_num : |(-2:ℝ)|<5/2) V F
  let W := nativeL2ParticularAngularCLM V F
  let w := nativeConjugatedJoint W
  let q := fun p : ℝ × S => V p.1*(Real.exp (2*p.1)*w p)
  have hw : Measurable w := nativeConjugatedJoint_measurable W
  have hq : Measurable q := (V.continuous.measurable.comp measurable_fst).mul
    ((Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul hw)
  have hs (t : ℝ) : (fun θ => q (t,θ))=ᵐ[angularVolume] ((V t • W t : AngularL2) : S → ℝ) := by
    have he : (V t*Real.exp (2*t)) • nativeConjugatedCurve W t=V t • W t := by
      unfold nativeConjugatedCurve
      rw [smul_smul]
      congr 1
      rw [mul_assoc,←Real.exp_add]
      ring_nf
      rw [Real.exp_zero,mul_one]
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp
      (Lp.coeFn_smul (V t*Real.exp (2*t)) (nativeConjugatedCurve W t))
    rw [he] at hc
    filter_upwards [nativeConjugatedJoint_ae W t,hc] with θ hw hc
    change w (t,θ)=_ at hw
    change V t*(Real.exp (2*t)*w (t,θ))=_
    rw [hw]
    have hh := hc (mem_univ θ)
    simp only [Pi.smul_apply,smul_eq_mul] at hh
    rw [hh]
    ring
  have hsource : ∀ᵐ t : ℝ ∂volume,(fun θ => q (t,θ))=ᵐ[angularVolume]
      (nativeHighProjection (angularBasis.repr.symm ((spectralL2PotentialMulCLM V U) t)) : S → ℝ) := by
    have hu := spectralL2PotentialContinuous_coe_ae nativeAngularRate (by norm_num : (0:ℝ)<5/2)
      nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hminus
      (by simpa only [neg_neg] using hplus) F
    filter_upwards [spectralL2PotentialMul_coe_ae V U,hu] with t hm hu
    change (spectralL2PotentialMulCLM V U) t=V t • U t at hm
    change spectralL2PotentialContinuousCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
      (by norm_num : |(-2:ℝ)|<5/2) V F t=U t at hu
    rw [hm,←hu,map_smul,map_smul]
    exact hs t
  have hr := nativeL2HighPhysicalSourceCLM_eq_lift (spectralL2PotentialMulCLM V U) hq hsource
  have hl := nativeCollarPotentialMulCLM_ae V (nativeL2ParticularValueCLM hκ0 hκ1 V hminus hplus F)
  have hv := nativeL2ParticularValueCLM_eq_lift hκ0 hκ1 V hminus hplus F hw (nativeConjugatedJoint_ae W)
  apply Lp.ext
  filter_upwards [hr,hl,hv] with x hr hl hv
  rw [hl,hv,hr]
  exact native_cylinderLift_potential_weight V w x

theorem nativeL2Particular_physical_equation
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    (∑ j : Fin 3,nativeL2ParticularSecondCLM hκ0 hκ1 V hminus hplus j j F)+
      nativeCollarPotentialMulCLM V (nativeL2ParticularValueCLM hκ0 hκ1 V hminus hplus F)=
        nativeL2HighPhysicalSourceCLM F := by
  rw [nativeL2Particular_all_source_laplacian hκ0 hκ1 V hminus hplus F,
    nativeL2Particular_potential_binding hκ0 hκ1 V hminus hplus F]
  change nativeL2HighPhysicalSourceCLM (F-spectralL2PotentialMulCLM V
    (spectralL2IntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
      (by norm_num : |(-2:ℝ)|<5/2) V F))+_= _
  rw [map_sub,sub_add_cancel]

theorem nativeL2Particular_physical_equation_eight
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    (-8:ℝ) • (∑ j : Fin 3,nativeL2ParticularSecondCLM hκ0 hκ1 V hminus hplus j j F)-
      (8:ℝ) • nativeCollarPotentialMulCLM V (nativeL2ParticularValueCLM hκ0 hκ1 V hminus hplus F)=
        (-8:ℝ) • nativeL2HighPhysicalSourceCLM F := by
  have h := congrArg (fun x => (-8:ℝ) • x) (nativeL2Particular_physical_equation hκ0 hκ1 V hminus hplus F)
  simpa only [smul_add,neg_smul,sub_eq_add_neg] using h

#print axioms native_cylinderLift_potential_weight
#print axioms nativeL2Particular_potential_binding
#print axioms nativeL2Particular_physical_equation
#print axioms nativeL2Particular_physical_equation_eight
end Yamabe3.Analysis.SpherePolar
