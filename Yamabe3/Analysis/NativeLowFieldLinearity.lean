import Yamabe3.Analysis.NativeFullPhysicalCollar

/-! Exact source linearity of the actual low future solution and its
finite entrance subtraction. No representative choice is declared linear. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SpherePolar SphereSpectrum UniformElliptic

variable (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0≤v t ∧ v t≤1)

theorem nativeLowSolvedCurve_add (F G:ℝ →ᵇ AngularL2) :
    nativeLowSolvedCurve v hv hb (F+G)=nativeLowSolvedCurve v hv hb F+nativeLowSolvedCurve v hv hb G := by
  have he:nativeLowSource (F+G)=nativeLowSource F+nativeLowSource G:=by
    apply BoundedContinuousFunction.ext
    intro t
    change nativeLowProjection (F t+G t)=nativeLowProjection (F t)+nativeLowProjection (G t)
    exact map_add _ _ _
  simp only [nativeLowSolvedCurve,he,map_add]

theorem nativeLowSolvedCurve_smul (c:ℝ) (F:ℝ →ᵇ AngularL2) :
    nativeLowSolvedCurve v hv hb (c • F)=c • nativeLowSolvedCurve v hv hb F := by
  have he:nativeLowSource (c • F)=c • nativeLowSource F:=by
    apply BoundedContinuousFunction.ext
    intro t
    change nativeLowProjection (c • F t)=c • nativeLowProjection (F t)
    exact map_smul _ _ _
  simp only [nativeLowSolvedCurve,he,map_smul]

theorem nativeLowZeroEntranceField_add (F G:ℝ →ᵇ AngularL2) :
    nativeLowZeroEntranceField v hv hb (F+G)=nativeLowZeroEntranceField v hv hb F+nativeLowZeroEntranceField v hv hb G := by
  funext x
  by_cases hx:x=0
  · simp [hx,nativeLowZeroEntranceField,finitePhysical,cylinderLift_zero]
  let y:puncturedSpace:=⟨x,hx⟩
  change finitePhysical _ _ (y:E)=finitePhysical _ _ (y:E)+finitePhysical _ _ (y:E)
  simp only [finitePhysical,cylinderLift_coe,puncturedCylinderLift,separableCylinder,
    nativeLowZeroEntranceCoefficient,nativeLowPhysicalCoefficient,nativeLowEntranceCoefficient,
    nativeLowSolvedCurve_add,BoundedContinuousFunction.add_apply,inner_add_right]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem nativeLowZeroEntranceField_smul (c:ℝ) (F:ℝ →ᵇ AngularL2) :
    nativeLowZeroEntranceField v hv hb (c • F)=c • nativeLowZeroEntranceField v hv hb F := by
  funext x
  by_cases hx:x=0
  · simp [hx,nativeLowZeroEntranceField,finitePhysical,cylinderLift_zero]
  let y:puncturedSpace:=⟨x,hx⟩
  change finitePhysical _ _ (y:E)=c*finitePhysical _ _ (y:E)
  simp only [finitePhysical,cylinderLift_coe,puncturedCylinderLift,separableCylinder,
    nativeLowZeroEntranceCoefficient,nativeLowPhysicalCoefficient,nativeLowEntranceCoefficient,
    nativeLowSolvedCurve_smul,BoundedContinuousFunction.smul_apply,inner_smul_right,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem nativeLowEntranceLift_add (F G:ℝ →ᵇ AngularL2) :
    nativeLowEntranceLift v hv hb (F+G)=nativeLowEntranceLift v hv hb F+nativeLowEntranceLift v hv hb G := by
  funext x
  simp only [nativeLowEntranceLift_basis,nativeLowSolvedCurve_add,BoundedContinuousFunction.add_apply,
    inner_add_right,add_mul,Finset.sum_add_distrib,Pi.add_apply]

theorem nativeLowEntranceLift_smul (c:ℝ) (F:ℝ →ᵇ AngularL2) :
    nativeLowEntranceLift v hv hb (c • F)=c • nativeLowEntranceLift v hv hb F := by
  funext x
  simp only [nativeLowEntranceLift_basis,nativeLowSolvedCurve_smul,BoundedContinuousFunction.smul_apply,
    inner_smul_right,smul_eq_mul,Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

#print axioms nativeLowSolvedCurve_add
#print axioms nativeLowSolvedCurve_smul
#print axioms nativeLowZeroEntranceField_add
#print axioms nativeLowZeroEntranceField_smul
#print axioms nativeLowEntranceLift_add
#print axioms nativeLowEntranceLift_smul
end Yamabe3.Analysis.Delaunay
