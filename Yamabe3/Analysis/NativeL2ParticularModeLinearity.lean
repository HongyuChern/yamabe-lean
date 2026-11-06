import Yamabe3.Analysis.NativeL2ParticularModeBudget
import Yamabe3.Analysis.SpectralIntegralLinearity

/-! The same finite physical mode is linear in the original source.
The potential inverse is the proved Banach fixed point, not a fresh choice. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
  (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)

theorem nativeL2ParticularMode_add (F G : ℝ →ᵇ SpectralSpace AngularIndex) (i : AngularIndex) :
    nativeL2ParticularMode hκ0 hκ1 V hminus (F+G) i=
      nativeL2ParticularMode hκ0 hκ1 V hminus F i+nativeL2ParticularMode hκ0 hκ1 V hminus G i := by
  classical
  unfold nativeL2ParticularMode
  split_ifs with hi
  · funext x
    simp only [nativeL2FiniteParticular,finitePhysical,Finset.sum_singleton,Pi.add_apply]
    by_cases hx : x=0
    · subst x
      simp only [cylinderLift_zero,add_zero]
    · let y : puncturedSpace := ⟨x,by change x≠0;exact hx⟩
      change cylinderLift _ (y:E)=cylinderLift _ (y:E)+cylinderLift _ (y:E)
      simp only [cylinderLift_coe,puncturedCylinderLift,separableCylinder,
        spectralIntegralPotentialInverse_add,BoundedContinuousFunction.coe_add,Pi.add_apply,lp.coeFn_add]
      ring
  · simp

theorem nativeL2ParticularMode_smul (c : ℝ) (F : ℝ →ᵇ SpectralSpace AngularIndex) (i : AngularIndex) :
    nativeL2ParticularMode hκ0 hκ1 V hminus (c • F) i=c • nativeL2ParticularMode hκ0 hκ1 V hminus F i := by
  classical
  unfold nativeL2ParticularMode
  split_ifs with hi
  · funext x
    simp only [nativeL2FiniteParticular,finitePhysical,Finset.sum_singleton,Pi.smul_apply,smul_eq_mul]
    by_cases hx : x=0
    · subst x
      simp only [cylinderLift_zero,mul_zero]
    · let y : puncturedSpace := ⟨x,by change x≠0;exact hx⟩
      change cylinderLift _ (y:E)=c*cylinderLift _ (y:E)
      simp only [cylinderLift_coe,puncturedCylinderLift,separableCylinder,
        spectralIntegralPotentialInverse_smul,BoundedContinuousFunction.coe_smul,Pi.smul_apply,lp.coeFn_smul,smul_eq_mul]
      ring
  · simp

#print axioms nativeL2ParticularMode_add
#print axioms nativeL2ParticularMode_smul
end Yamabe3.Analysis.SpherePolar
