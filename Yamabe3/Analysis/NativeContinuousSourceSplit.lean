import Yamabe3.Analysis.NativeFiniteLowProjection
import Yamabe3.Analysis.NativeLowPhysicalField
import Yamabe3.Analysis.NativeCylinderSourceSpace
import Yamabe3.Analysis.Cylinder.NativeProjectedC2PhysicalEquation

/-! The actual continuous low representative and complementary high
representative of the very same source. Their sum is the original scalar
function pointwise, not just a chosen L2 class. This module makes no H2
projection claim. Regularity of a subsequent sum must use the original
full source and its actual weak equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold Topology ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.SphereSpectrum Yamabe3.Analysis.SpherePolar
open Poincare.Geometry.Riemannian.SpaceForm

def nativeLowSourceCylinder (F : ℝ →ᵇ AngularL2) : CylinderSource :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p : ℝ × S => nativeLowRepresentativeCLM (F p.1) p.2)
    (continuous_eval.comp
      (((nativeLowRepresentativeCLM.continuous.comp F.continuous).comp continuous_fst).prodMk
        continuous_snd))
    (‖nativeLowRepresentativeCLM‖*‖F‖) (fun p => by
      exact ((ContinuousMap.norm_coe_le_norm _ p.2).trans
        (nativeLowRepresentativeCLM.le_opNorm _)).trans
        (mul_le_mul_of_nonneg_left (F.norm_coe_le_norm p.1) (norm_nonneg _)))

def nativeLowSourceCylinderCLM : (ℝ →ᵇ AngularL2) →L[ℝ] CylinderSource :=
  LinearMap.mkContinuous
    { toFun := nativeLowSourceCylinder
      map_add' := by
        intro F G
        apply BoundedContinuousFunction.ext
        intro p
        change nativeLowRepresentativeCLM (F p.1+G p.1) p.2 = _
        rw [map_add]
        rfl
      map_smul' := by
        intro c F
        apply BoundedContinuousFunction.ext
        intro p
        change nativeLowRepresentativeCLM (c • F p.1) p.2 = _
        rw [map_smul]
        rfl }
    ‖nativeLowRepresentativeCLM‖ (fun F => by
      change ‖nativeLowSourceCylinder F‖ ≤ ‖nativeLowRepresentativeCLM‖*‖F‖
      apply (BoundedContinuousFunction.norm_le (f:=nativeLowSourceCylinder F)
        (mul_nonneg (norm_nonneg nativeLowRepresentativeCLM) (norm_nonneg F))).mpr
      exact (fun p : ℝ × S => ((ContinuousMap.norm_coe_le_norm _ p.2).trans
          (nativeLowRepresentativeCLM.le_opNorm _)).trans
          (mul_le_mul_of_nonneg_left (F.norm_coe_le_norm p.1) (norm_nonneg _))))

theorem nativeLowSourceCylinder_ae (F : ℝ →ᵇ AngularL2) (t : ℝ) :
    (fun θ => nativeLowSourceCylinder F (t,θ)) =ᵐ[angularVolume]
      (nativeLowProjection (F t) : S → ℝ) := nativeLowRepresentativeCLM_ae (F t)

def nativeHighSourceCylinder (G : CylinderSource) : CylinderSource :=
  G-nativeLowSourceCylinder (cylinderToAngularL2CLM G)

theorem nativeHighSourceCylinder_ae (G : CylinderSource) (t : ℝ) :
    (fun θ => nativeHighSourceCylinder G (t,θ)) =ᵐ[angularVolume]
      (nativeHighProjection (cylinderToAngularL2CLM G t) : S → ℝ) := by
  let U := cylinderToAngularL2CLM G t
  have hsub := (ae_restrict_iff' MeasurableSet.univ).mp (Lp.coeFn_sub U (nativeLowProjection U))
  have he : U-nativeLowProjection U = nativeHighProjection U := by
    have hh := nativeHighProjection_add_low U
    exact sub_eq_iff_eq_add.mpr hh.symm
  have hg := cylinderTestL2_ae G G.continuous t
  change (U : S → ℝ) =ᵐ[angularVolume] (fun θ => G (t,θ)) at hg
  filter_upwards [hg,nativeLowSourceCylinder_ae (cylinderToAngularL2CLM G) t,hsub] with θ hG hL hs
  change G (t,θ)-nativeLowSourceCylinder (cylinderToAngularL2CLM G) (t,θ) = _
  rw [← hG,hL]
  have h := hs (mem_univ θ)
  rw [he] at h
  exact h.symm

theorem nativeSourceCylinder_split (G : CylinderSource) (p : ℝ × S) :
    nativeHighSourceCylinder G p+nativeLowSourceCylinder (cylinderToAngularL2CLM G) p=G p := by
  change (G p-nativeLowSourceCylinder (cylinderToAngularL2CLM G) p)+
    nativeLowSourceCylinder (cylinderToAngularL2CLM G) p=G p
  ring

theorem nativeLowSource_finite_weighted_eq (F : ℝ →ᵇ AngularL2) (p : ℝ × S) :
    finiteAngular nativeLowIndexFinset
      (fun i t => Real.exp (-2*t)*inner ℝ (angularBasis i) (nativeLowSource F t)) p =
      Real.exp (-2*p.1)*nativeLowSourceCylinder F p := by
  change (∑ i ∈ nativeLowIndexFinset,
    (Real.exp (-2*p.1)*inner ℝ (angularBasis i) (nativeLowSource F p.1))*angularRepresentative i p.2) =
    Real.exp (-2*p.1)*nativeLowRepresentativeCLM (F p.1) p.2
  rw [nativeLowRepresentativeCLM_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [nativeLowSource,nativeProjectedSource_coefficient,if_pos (mem_nativeLowIndexFinset i |>.mp hi)]
  ring

theorem nativePhysicalForcing_source_split (G : CylinderSource) (x : E) :
    physicalForcing (fun p : ℝ × S => Real.exp (-2*p.1)*nativeHighSourceCylinder G p) x+
      physicalForcing (fun p : ℝ × S => Real.exp (-2*p.1)*
        nativeLowSourceCylinder (cylinderToAngularL2CLM G) p) x =
      physicalForcing (fun p : ℝ × S => Real.exp (-2*p.1)*G p) x := by
  rw [physicalForcing_expNegTwo,physicalForcing_expNegTwo,physicalForcing_expNegTwo]
  by_cases hx : x=0
  · simp [hx,cylinderLift_zero]
  let y : puncturedSpace := ⟨x,hx⟩
  change -8*cylinderLift (nativeHighSourceCylinder G) (y:E)+
    -8*cylinderLift (nativeLowSourceCylinder (cylinderToAngularL2CLM G)) (y:E)=
    -8*cylinderLift G (y:E)
  simp only [cylinderLift_coe,puncturedCylinderLift]
  have h := nativeSourceCylinder_split G (cylinderCoordinates y)
  linear_combination (-8*radialScale ‖(y:E)‖)*h

#print axioms nativeLowSourceCylinderCLM
#print axioms nativeHighSourceCylinder_ae
#print axioms nativeSourceCylinder_split
#print axioms nativeLowSource_finite_weighted_eq
#print axioms nativePhysicalForcing_source_split
end Yamabe3.Analysis.Delaunay
