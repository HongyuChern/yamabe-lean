import Yamabe3.Analysis.NativeL2ParticularModeBudget
import Yamabe3.Analysis.NativeL2ParticularIdentity

/-! The actual finite physical equation has exactly the original
residual F - V U. The exp(-2t) conjugation cancels the radial inverse-square
factor in the Laplacian. Low auxiliary rates remain explicitly projected. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem native_cylinderLift_conjugated_div_norm_sq (w : ℝ × S → ℝ) {x : E} (hx : x≠0) :
    cylinderLift (fun p => Real.exp (-2*p.1)*w p) x/‖x‖^2=cylinderLift w x := by
  let y : puncturedSpace := ⟨x,by change x≠0;exact hx⟩
  change cylinderLift (fun p => Real.exp (-2*p.1)*w p) (y:E)/‖x‖^2=cylinderLift w (y:E)
  rw [cylinderLift_coe,cylinderLift_coe]
  have hn : 0<‖x‖ := norm_pos_iff.mpr hx
  have he : Real.exp (-2*(-Real.log ‖x‖))=‖x‖^2 := by
    calc
      _ = Real.exp (Real.log ‖x‖+Real.log ‖x‖) := by congr 1;ring
      _ = _ := by rw [Real.exp_add,Real.exp_log hn,pow_two]
  change radialScale ‖x‖*(Real.exp (-2*(-Real.log ‖x‖))*w (cylinderCoordinates y))/‖x‖^2=
    radialScale ‖x‖*w (cylinderCoordinates y)
  rw [he]
  field_simp [hn.ne']

variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
  (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)
  (F : ℝ →ᵇ SpectralSpace AngularIndex)

def nativeL2ParticularResidualCurve (t : ℝ) : AngularL2 :=
  nativeHighProjection (angularBasis.repr.symm (F t-V t •
    spectralIntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
      (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hminus F t))

theorem nativeL2ParticularResidualCurve_continuous :
    Continuous (nativeL2ParticularResidualCurve hκ0 hκ1 V hminus F) :=
  nativeHighProjection.continuous.comp (angularBasis.repr.symm.continuous.comp
    (F.continuous.sub (V.continuous.smul
      (spectralIntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
        (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hminus F).continuous)))

theorem nativeL2ParticularResidualCurve_coefficient (i : AngularIndex) (t : ℝ) :
    inner ℝ (angularBasis i) (nativeL2ParticularResidualCurve hκ0 hκ1 V hminus F t)=
      if 6≤angularEigenvalue i then F t i-V t*
        spectralIntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
          (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hminus F t i else 0 := by
  unfold nativeL2ParticularResidualCurve
  rw [nativeHighProjection,nativeAngularProjection_coefficient,←HilbertBasis.repr_apply_apply,
    LinearIsometryEquiv.apply_symm_apply]
  split_ifs <;> rfl

theorem nativeL2Particular_finite_laplacian (s : Finset AngularIndex) (x : E) (hx : x≠0) :
    nativeCoordinateLaplacian (fun y => ∑ i ∈ s,nativeL2ParticularMode hκ0 hκ1 V hminus F i y) x=
      cylinderLift (projectedAngular s (nativeL2ParticularResidualCurve hκ0 hκ1 V hminus F)) x := by
  classical
  let U := spectralIntegralPotentialInverse nativeAngularRate (by norm_num : (0:ℝ)<5/2)
    nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hminus F
  let q := fun i t => Real.exp (-2*t)*U t i
  let s' := s.filter (fun i => 6≤angularEigenvalue i)
  have ho (i : AngularIndex) := spectralIntegralPotentialInverse_physical_coordinate_C2 nativeAngularRate
    (by norm_num : (0:ℝ)<5/2) nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2)
    hκ0 hκ1 V hminus F i
  rw [nativeL2ParticularMode_sum]
  change nativeCoordinateLaplacian (finitePhysical s' q) x=_
  rw [native_finitePhysical_laplacian s' q (fun i _ => (ho i).1) hx]
  have he : finiteAngular s' (finiteTimeLaplacian q)=
      fun p => Real.exp (-2*p.1)*projectedAngular s (nativeL2ParticularResidualCurve hκ0 hκ1 V hminus F) p := by
    funext p
    unfold projectedAngular
    simp_rw [nativeL2ParticularResidualCurve_coefficient]
    unfold finiteAngular
    rw [Finset.mul_sum]
    change (∑ i ∈ s.filter (fun i => 6≤angularEigenvalue i),finiteTimeLaplacian q i p.1*angularRepresentative i p.2)=_
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with h
    · have hq : finiteTimeLaplacian q i p.1=Real.exp (-2*p.1)*(F p.1 i-V p.1*U p.1 i) := by
        change deriv (deriv (q i)) p.1-(angularEigenvalue i+1/4)*q i p.1=_
        rw [←show nativeAngularRate i^2=angularEigenvalue i+1/4 by rw [nativeAngularRate_sq,max_eq_right h]]
        exact (ho i).2 p.1
      rw [hq]
      simp only [if_pos h]
      dsimp only [U]
      ring
    · simp [h]
  rw [he,native_cylinderLift_conjugated_div_norm_sq _ hx]

#print axioms native_cylinderLift_conjugated_div_norm_sq
#print axioms nativeL2ParticularResidualCurve_coefficient
#print axioms nativeL2Particular_finite_laplacian
end Yamabe3.Analysis.SpherePolar
