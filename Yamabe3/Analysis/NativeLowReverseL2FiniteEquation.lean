import Yamabe3.Analysis.NativeLowReverseL2SameField
import Yamabe3.Analysis.NativeLowL2FiniteEquation

/-! Exact physical equation of the reversed low solution on the dense
source domain. Reflection changes the source by |x|^-4; that factor is
proved here and is not discarded in the subsequent L2 extension. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)

def nativeLowReversePotential : ℝ →ᵇ ℝ :=
  (delaunayPhasePotentialBCF v hv hb 0).compContinuous ⟨Neg.neg,continuous_neg⟩

theorem native_cylinderLift_exp_four (w : ℝ×S→ℝ) {x : E} (hx : x≠0) :
    cylinderLift (fun p => Real.exp (4*p.1)*w p) x=(‖x‖^4)⁻¹*cylinderLift w x := by
  let y : puncturedSpace := ⟨x,by change x≠0;exact hx⟩
  have hn : 0<‖x‖ := norm_pos_iff.mpr hx
  have he : Real.exp (4*(-Real.log ‖x‖))=(‖x‖^4)⁻¹ := by
    calc
      _=Real.exp (-(Real.log ‖x‖+Real.log ‖x‖+Real.log ‖x‖+Real.log ‖x‖)) := by congr 1;ring
      _=_ := by rw [Real.exp_neg];simp only [Real.exp_add,Real.exp_log hn];ring
  change cylinderLift _ (y:E)=(‖x‖^4)⁻¹*cylinderLift w (y:E)
  rw [cylinderLift_coe,cylinderLift_coe]
  change radialScale ‖x‖*(Real.exp (4*(-Real.log ‖x‖))*w (cylinderCoordinates y))=
    (‖x‖^4)⁻¹*(radialScale ‖x‖*w (cylinderCoordinates y))
  rw [he]
  ring

private theorem lift_div (w : ℝ×S→ℝ) {x : E} (hx : x≠0) :
    cylinderLift (fun p => Real.exp (2*p.1)*w p) x/‖x‖^2=
      cylinderLift (fun p => Real.exp (4*p.1)*w p) x := by
  have he : (fun p : ℝ×S => Real.exp (-2*p.1)*(Real.exp (4*p.1)*w p))=
      (fun p : ℝ×S => Real.exp (2*p.1)*w p) := by
    funext p
    rw [←mul_assoc,←Real.exp_add,show -2*p.1+4*p.1=2*p.1 by ring]
  have h := native_cylinderLift_conjugated_div_norm_sq (fun p => Real.exp (4*p.1)*w p) hx
  rw [he] at h
  exact h

theorem nativeLowReverseL2_finite_physical_equation (F : ℝ →ᵇ AngularSpectralSpace) (hF : MemLp F 2)
    {x : E} (hx : x≠0) :
    nativeCoordinateLaplacian (nativeLowReverseL2PhysicalField v hv hb (hF.toLp F)) x+
      nativeHalfEndPotentialCoefficient (nativeLowReversePotential v hv hb) x*
        nativeLowReverseL2PhysicalField v hv hb (hF.toLp F) x=
      (‖x‖^4)⁻¹*cylinderLift (finiteAngular nativeLowIndexFinset (fun i t => F (-t) i)) x := by
  let U := lowL2ContinuousCLM (lowAngularOperatorBCF v hv hb) (lowAngularOperatorBCF_norm_le v hv hb) (hF.toLp F)
  let V := nativeLowReversePotential v hv hb
  let q := fun i t => Real.exp (2*t)*U (-t) i
  have hVa (t : ℝ) : V t=(15/4)*v (-t)^4 := by
    simp only [V,nativeLowReversePotential,BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_mk,delaunayPhasePotentialBCF_apply,add_zero]
  have hq (i : AngularIndex) (hi : i∈nativeLowIndexFinset) :=
    nativeLowL2_reversed_coefficient_C2 v hv hb F hF i ((mem_nativeLowIndexFinset i).mp hi)
  have he : finiteAngular nativeLowIndexFinset (finiteTimeLaplacian q)=
      fun p => Real.exp (2*p.1)*finiteAngular nativeLowIndexFinset (fun i t => F (-t) i-V t*U (-t) i) p := by
    funext p
    unfold finiteAngular
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hqi : finiteTimeLaplacian q i p.1=Real.exp (2*p.1)*(F (-p.1) i-V p.1*U (-p.1) i) := by
      change deriv (deriv (q i)) p.1-(angularEigenvalue i+1/4)*q i p.1=_
      rw [(hq i hi).2 p.1]
      change (angularEigenvalue i+1/4-(15/4)*v (-p.1)^4)*(Real.exp (2*p.1)*U (-p.1) i)+
        Real.exp (2*p.1)*F (-p.1) i-(angularEigenvalue i+1/4)*(Real.exp (2*p.1)*U (-p.1) i)=_
      rw [hVa];ring
    rw [hqi];ring
  have hp : (fun p : ℝ×S => V p.1*(Real.exp (2*p.1)*finiteAngular nativeLowIndexFinset q p))=
      fun p => Real.exp (4*p.1)*finiteAngular nativeLowIndexFinset (fun i t => V t*U (-t) i) p := by
    funext p
    unfold finiteAngular
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have ee : Real.exp (2*p.1)*Real.exp (2*p.1)=Real.exp (4*p.1) := by rw [←Real.exp_add];congr 1;ring
    dsimp only [q]
    calc
      _=(Real.exp (2*p.1)*Real.exp (2*p.1))*(V p.1*U (-p.1) i*angularRepresentative i p.2) := by ring
      _=_ := by rw [ee]
  change nativeCoordinateLaplacian (finitePhysical nativeLowIndexFinset q) x+
    nativeHalfEndPotentialCoefficient V x*finitePhysical nativeLowIndexFinset q x=_
  rw [native_finitePhysical_laplacian _ q (fun i hi => (hq i hi).1) hx,he,lift_div _ hx,
    finitePhysical_eq_lift,native_cylinderLift_potential_weight,hp,
    native_cylinderLift_exp_four _ hx,native_cylinderLift_exp_four _ hx,←mul_add]
  congr 1
  rw [←congrFun (native_cylinderLift_add
    (finiteAngular nativeLowIndexFinset (fun i t => F (-t) i-V t*U (-t) i))
    (finiteAngular nativeLowIndexFinset (fun i t => V t*U (-t) i))) x]
  congr 1
  funext p
  unfold finiteAngular
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

#print axioms native_cylinderLift_exp_four
#print axioms nativeLowReverseL2_finite_physical_equation
end Yamabe3.Analysis.SpherePolar
