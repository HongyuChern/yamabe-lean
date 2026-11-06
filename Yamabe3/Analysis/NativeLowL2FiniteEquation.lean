import Yamabe3.Analysis.NativeLowL2SameField
import Yamabe3.Analysis.NativeL2PotentialBinding
import Yamabe3.Analysis.NativeL2FullSource

/-! The low L2 solver satisfies the actual model equation on its dense
continuous-source domain. The source retains the same low projection;
the inverse-square potential and exp(-2t) weights cancel exactly. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0 ≤ v t ∧ v t ≤ 1)

theorem nativeLowL2_finite_physical_equation (F : ℝ →ᵇ AngularSpectralSpace) (hF : MemLp F 2)
    {x : E} (hx : x≠0) :
    nativeCoordinateLaplacian (nativeLowL2PhysicalField v hv hb (hF.toLp F)) x+
      nativeHalfEndPotentialCoefficient (delaunayPhasePotentialBCF v hv hb 0) x*
        nativeLowL2PhysicalField v hv hb (hF.toLp F) x=
      cylinderLift (finiteAngular nativeLowIndexFinset (fun i t => F t i)) x := by
  let U := lowL2ContinuousCLM (lowAngularOperatorBCF v hv hb) (lowAngularOperatorBCF_norm_le v hv hb) (hF.toLp F)
  let V := delaunayPhasePotentialBCF v hv hb 0
  let q := fun i t => Real.exp (-2*t)*U t i
  have hVa (t : ℝ) : V t=(15/4)*v t^4 := by simp only [V,delaunayPhasePotentialBCF_apply,add_zero]
  have hq (i : AngularIndex) (hi : i∈nativeLowIndexFinset) :=
    nativeLowL2_weighted_coefficient_C2 v hv hb F hF i ((mem_nativeLowIndexFinset i).mp hi)
  have he : finiteAngular nativeLowIndexFinset (finiteTimeLaplacian q)=
      fun p => Real.exp (-2*p.1)*finiteAngular nativeLowIndexFinset (fun i t => F t i-V t*U t i) p := by
    funext p
    unfold finiteAngular
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hqi : finiteTimeLaplacian q i p.1=Real.exp (-2*p.1)*(F p.1 i-V p.1*U p.1 i) := by
      change deriv (deriv (q i)) p.1-(angularEigenvalue i+1/4)*q i p.1=_
      rw [(hq i hi).2 p.1]
      change (angularEigenvalue i+1/4-(15/4)*v p.1^4)*(Real.exp (-2*p.1)*U p.1 i)+
        Real.exp (-2*p.1)*F p.1 i-(angularEigenvalue i+1/4)*(Real.exp (-2*p.1)*U p.1 i)=_
      rw [hVa]
      ring
    rw [hqi]
    ring
  have hp : (fun p : ℝ × S => V p.1*(Real.exp (2*p.1)*finiteAngular nativeLowIndexFinset q p))=
      finiteAngular nativeLowIndexFinset (fun i t => V t*U t i) := by
    funext p
    unfold finiteAngular
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [q]
    have ee : Real.exp (2*p.1)*Real.exp (-2*p.1)=1 := by rw [←Real.exp_add];ring_nf;rw [Real.exp_zero]
    calc
      _=V p.1*(Real.exp (2*p.1)*Real.exp (-2*p.1))*U p.1 i*angularRepresentative i p.2 := by ring
      _=_ := by rw [ee];ring
  change nativeCoordinateLaplacian (finitePhysical nativeLowIndexFinset q) x+
    nativeHalfEndPotentialCoefficient V x*finitePhysical nativeLowIndexFinset q x=_
  rw [native_finitePhysical_laplacian _ q (fun i hi => (hq i hi).1) hx,he,
    native_cylinderLift_conjugated_div_norm_sq _ hx,finitePhysical_eq_lift,
    native_cylinderLift_potential_weight,hp]
  rw [←congrFun (native_cylinderLift_add
    (finiteAngular nativeLowIndexFinset (fun i t => F t i-V t*U t i))
    (finiteAngular nativeLowIndexFinset (fun i t => V t*U t i))) x]
  congr 1
  funext p
  unfold finiteAngular
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem nativeLowL2_finite_source_ae (F : ℝ →ᵇ AngularSpectralSpace) (t : ℝ) :
    (fun θ => finiteAngular nativeLowIndexFinset (fun i s => F s i) (t,θ))=ᵐ[angularVolume]
      (nativeLowProjection (angularBasis.repr.symm (F t)) : S → ℝ) := by
  have he : (∑ i ∈ nativeLowIndexFinset,F t i • angularBasis i)=nativeLowProjection (angularBasis.repr.symm (F t)) := by
    rw [nativeLowProjection_eq_finite,finiteHilbertProjection]
    apply Finset.sum_congr rfl
    intro i hi
    rw [←HilbertBasis.repr_apply_apply,LinearIsometryEquiv.apply_symm_apply]
  have h := finiteAngular_ae nativeLowIndexFinset (fun i s => F s i) t
  rw [he] at h
  exact h

#print axioms nativeLowL2_finite_physical_equation
#print axioms nativeLowL2_finite_source_ae
end Yamabe3.Analysis.SpherePolar
