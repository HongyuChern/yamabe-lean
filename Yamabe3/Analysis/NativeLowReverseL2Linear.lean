import Yamabe3.Analysis.NativeLowReverseL2Collar
import Yamabe3.Analysis.NativeCollarJetSpace
import Yamabe3.Analysis.L2ContinuousSourceModule

/-! The physical low field and its genuine C2 collar jets are linear in
one common source. This precedes their extension to all L2 data. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0 ≤ v t ∧ v t ≤ 1)

theorem nativeLowReverseL2PhysicalField_add (F G : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeLowReverseL2PhysicalField v hv hb (F+G)=nativeLowReverseL2PhysicalField v hv hb F+nativeLowReverseL2PhysicalField v hv hb G := by
  funext x
  simp only [nativeLowReverseL2PhysicalField,finitePhysical,Pi.add_apply,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x=0
  · subst x
    simp only [cylinderLift_zero,add_zero]
  · let y : puncturedSpace := ⟨x,by change x≠0;exact hx⟩
    change cylinderLift _ (y:E)=cylinderLift _ (y:E)+cylinderLift _ (y:E)
    simp only [cylinderLift_coe,puncturedCylinderLift,separableCylinder,
      map_add,BoundedContinuousFunction.coe_add,Pi.add_apply,lp.coeFn_add]
    ring

theorem nativeLowReverseL2PhysicalField_smul (c : ℝ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeLowReverseL2PhysicalField v hv hb (c • F)=c • nativeLowReverseL2PhysicalField v hv hb F := by
  funext x
  simp only [nativeLowReverseL2PhysicalField,finitePhysical,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x=0
  · subst x
    simp only [cylinderLift_zero,mul_zero]
  · let y : puncturedSpace := ⟨x,by change x≠0;exact hx⟩
    change cylinderLift _ (y:E)=c*cylinderLift _ (y:E)
    simp only [cylinderLift_coe,puncturedCylinderLift,separableCylinder,
      map_smul,BoundedContinuousFunction.coe_smul,Pi.smul_apply,lp.coeFn_smul,smul_eq_mul]
    ring

def nativeLowReverseL2PhysicalLinear : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun := nativeLowReverseL2PhysicalField v hv hb
  map_add' := nativeLowReverseL2PhysicalField_add v hv hb
  map_smul' := nativeLowReverseL2PhysicalField_smul v hv hb

def nativeLowReverseL2ContinuousFieldLinear : continuousL2Source AngularSpectralSpace →ₗ[ℝ] nativeC2OffZero :=
  ((nativeLowReverseL2PhysicalLinear v hv hb).comp (continuousL2SourceInclusion AngularSpectralSpace)).codRestrict
    nativeC2OffZero (fun F => (nativeLowReverseL2Physical_collar_energy v hv hb F.val F.property).1)

def nativeLowReverseL2C2JetLinear : continuousL2Source AngularSpectralSpace →ₗ[ℝ] NativeCollarJet :=
  nativeC2CollarJetLinear.comp (nativeLowReverseL2ContinuousFieldLinear v hv hb)

#print axioms nativeLowReverseL2PhysicalField_add
#print axioms nativeLowReverseL2PhysicalField_smul
#print axioms nativeLowReverseL2ContinuousFieldLinear
#print axioms nativeLowReverseL2C2JetLinear
end Yamabe3.Analysis.SpherePolar
