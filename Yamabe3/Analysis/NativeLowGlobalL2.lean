import Yamabe3.Analysis.NativeFullModelH1
import Yamabe3.Analysis.Cylinder.NativeHalfEndGlobalProjection
import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndPotentialL2

/-! Actual global L2 of the low source and the inverse-square potential
product of the constructed low field. No boundedness of the singular
physical potential is assumed. Its time weight cancels the decay of the
same low solution before using the genuine polar L2 identity. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SpherePolar SphereSpectrum UniformElliptic
local notation "O" => Metric.ball (0:E) 1 \ {(0:E)}

theorem nativeCylinderSource_lift_memLp (G:CylinderSource) :
    MemLp (cylinderLift G) 2 (volume.restrict O) := by
  let U:=cylinderToAngularL2CLM G
  have hae (t:ℝ) : (fun θ=>G (t,θ)) =ᵐ[angularVolume] (U t:S→ℝ) :=
    (cylinderTestL2_ae G G.continuous t).symm
  exact (native_halfEnd_lift_memLp_of_weighted_integrable G.continuous.measurable hae
    (native_halfEnd_weighted_norm_integrable_of_bound U.continuous ‖U‖
      (fun t _=>U.norm_coe_le_norm t))).1

theorem nativeCylinderSource_physical_memLp (G:CylinderSource) :
    MemLp (physicalForcing (fun p:ℝ × S=>Real.exp (-2*p.1)*G p)) 2
      (volume.restrict O) := by
  have he : physicalForcing (fun p:ℝ × S=>Real.exp (-2*p.1)*G p)=
      fun x=> -8*cylinderLift G x := funext (physicalForcing_expNegTwo G)
  rw [he]
  exact (nativeCylinderSource_lift_memLp G).const_mul (-8)

def nativeCylinderSourcePotentialProduct (V:ℝ →ᵇ ℝ) (G:CylinderSource) : CylinderSource :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun p:ℝ × S=>V p.1*G p)
    ((V.continuous.comp continuous_fst).mul G.continuous) (‖V‖*‖G‖)
    (fun p => by
      rw [norm_mul]
      exact mul_le_mul (V.norm_coe_le_norm p.1) (G.norm_coe_le_norm p)
        (norm_nonneg _) (norm_nonneg _))

theorem nativeLowPhysicalField_eq_weighted_lift (v:ℝ→ℝ) (hv:Continuous v)
    (hb:∀t,0≤v t ∧ v t≤1) (F:ℝ →ᵇ AngularL2) :
    nativeLowPhysicalField v hv hb F = cylinderLift
      (fun p:ℝ × S=>Real.exp (-2*p.1)*
        nativeLowSourceCylinder (nativeLowSolvedCurve v hv hb F) p) := by
  rw [nativeLowPhysicalField,finitePhysical_eq_lift]
  congr 1
  funext p
  change (∑i∈nativeLowIndexFinset,
    (Real.exp (-2*p.1)*inner ℝ (angularBasis i) (nativeLowSolvedCurve v hv hb F p.1))*
      angularRepresentative i p.2)=
    Real.exp (-2*p.1)*nativeLowRepresentativeCLM (nativeLowSolvedCurve v hv hb F p.1) p.2
  rw [nativeLowRepresentativeCLM_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem nativePotential_weighted_lift_eq (V:ℝ →ᵇ ℝ) (G:CylinderSource) (x:E) :
    nativeHalfEndPotentialCoefficient V x*
      cylinderLift (fun p:ℝ × S=>Real.exp (-2*p.1)*G p) x=
      cylinderLift (nativeCylinderSourcePotentialProduct V G) x := by
  rw [nativeHalfEndPotentialCoefficient_mul_cylinderLift]
  congr 1
  funext p
  change Real.exp (2*p.1)*V p.1*(Real.exp (-2*p.1)*G p)=V p.1*G p
  calc
    _ = (Real.exp (2*p.1)*Real.exp (-2*p.1))*(V p.1*G p) := by ring
    _ = _ := by rw [←Real.exp_add]; simp

theorem nativeLowPhysicalField_potential_memLp (v:ℝ→ℝ) (hv:Continuous v)
    (hb:∀t,0≤v t ∧ v t≤1) (F:ℝ →ᵇ AngularL2) (V:ℝ →ᵇ ℝ) :
    MemLp (fun x:E=>nativeHalfEndPotentialCoefficient V x*nativeLowPhysicalField v hv hb F x)
      2 (volume.restrict O) := by
  rw [nativeLowPhysicalField_eq_weighted_lift]
  have he:=funext (nativePotential_weighted_lift_eq V
    (nativeLowSourceCylinder (nativeLowSolvedCurve v hv hb F)))
  rw [he]
  exact nativeCylinderSource_lift_memLp _

#print axioms nativeCylinderSource_lift_memLp
#print axioms nativeCylinderSource_physical_memLp
#print axioms nativeLowPhysicalField_eq_weighted_lift
#print axioms nativePotential_weighted_lift_eq
#print axioms nativeLowPhysicalField_potential_memLp
end Yamabe3.Analysis.Delaunay
