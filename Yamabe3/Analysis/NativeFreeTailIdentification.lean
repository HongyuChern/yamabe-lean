import Yamabe3.Analysis.NativeFreeTailH2
import Yamabe3.Analysis.NativeCollarSeriesLocalIdentification
import Yamabe3.Analysis.NativeL2ShiftedCollar
import Yamabe3.Analysis.SpectralBoundaryPoissonL2

/-! All free tail collars represent literal weighted dilations of one
joint measurable physical field. A local finite identity suffices; the
negative-time even extension is not assigned a homogeneous equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeFreeBoundaryAngular (b : SpectralSpace AngularIndex) : ℝ →ᵇ AngularL2 :=
  (nativeHighProjection.compLeftContinuousBounded ℝ)
    (angularSynthesisCLM (spectralFullBoundaryPoissonCLM nativeAngularRate (by norm_num) nativeAngularRate_lower b))

 theorem nativeFreeBoundary_shifted_coefficient (b : SpectralSpace AngularIndex)
    (s t : ℝ) (hst : 0 ≤ t+s) (i : AngularIndex) :
    inner ℝ (angularBasis i) (nativeConjugatedCurve
      (boundedTimeTranslate AngularL2 s (nativeFreeBoundaryAngular b)) t)=nativeFreeTailCoefficient s b i t := by
  change inner ℝ (angularBasis i) (Real.exp (-2*t) • nativeHighProjection
    (angularBasis.repr.symm (spectralFullBoundaryPoissonCLM nativeAngularRate (by norm_num)
      nativeAngularRate_lower b (t+s))))=_
  rw [real_inner_smul_right,nativeHighProjection,nativeAngularProjection_coefficient,
    ←HilbertBasis.repr_apply_apply,LinearIsometryEquiv.apply_symm_apply,
    spectralFullBoundaryPoissonCLM_coordinate,abs_of_nonneg hst]
  unfold nativeFreeTailCoefficient
  split_ifs
  · rw [←mul_assoc,←Real.exp_add]
    congr 2
    ring
  · simp only [mul_zero]

 theorem nativeFreeTail_projected_lift (b : SpectralSpace AngularIndex) (s : ℝ) (hs : 1 ≤ s)
    (m : Finset AngularIndex) (x : E) (hx : x∈nativePoissonEntranceCollar) :
    cylinderLift (projectedAngular m (nativeConjugatedCurve
      (boundedTimeTranslate AngularL2 s (nativeFreeBoundaryAngular b)))) x=
        ∑ i ∈ m,nativeFreeTailMode s b i x := by
  rw [show (∑ i ∈ m,nativeFreeTailMode s b i x)=finitePhysical m (nativeFreeTailCoefficient s b) x
    from congrFun (nativeFreeTailMode_sum s b m) x,finitePhysical_eq_lift]
  let y : puncturedSpace := ⟨x,hx.1⟩
  change cylinderLift _ (y:E)=cylinderLift _ (y:E)
  rw [cylinderLift_coe,cylinderLift_coe]
  unfold puncturedCylinderLift projectedAngular finiteAngular
  apply congrArg (fun a : ℝ => radialScale ‖(y:E)‖*a)
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact nativeFreeBoundary_shifted_coefficient b s (-Real.log ‖x‖)
    (by have ht := hx.2.1;linarith) i

 theorem nativeFreeTailValue_same_dilation (b : SpectralSpace AngularIndex)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume]
      (nativeConjugatedCurve (nativeFreeBoundaryAngular b) t : S → ℝ))
    (s : ℝ) (hs : 1 ≤ s) :
    (nativeFreeTailValue s b : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) := by
  let W := boundedTimeTranslate AngularL2 s (nativeFreeBoundaryAngular b)
  have hrep : ∀ t,(fun θ => weightedCylinderShift s w (t,θ))=ᵐ[angularVolume]
      (nativeConjugatedCurve W t : S → ℝ) := by
    intro t
    change _=ᵐ[angularVolume] (nativeConjugatedCurve
      (boundedTimeTranslate AngularL2 s (nativeFreeBoundaryAngular b)) t : S → ℝ)
    rw [nativeConjugatedCurve_translate]
    exact weightedCylinderShift_representation s hae t
  have h := nativeCollarSeries_eq_lift_on_collar _ (nativeFreeTailMode_C2 s b)
    (nativeFreeTail_summable s hs b).1 _ (nativeConjugatedCurve_continuous W)
    (nativeFreeTail_projected_lift b s hs) (weightedCylinderShift_measurable s hw) hrep
  filter_upwards [h] with x hx
  exact hx.trans (cylinderLift_weightedCylinderShift s w x)

 theorem exists_nativeFreeTail_same_all_scale_field (b : SpectralSpace AngularIndex) :
    ∃ w : ℝ × S → ℝ,Measurable w ∧
      (∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume]
        (nativeConjugatedCurve (nativeFreeBoundaryAngular b) t : S → ℝ)) ∧
      ∀ s : ℝ,1 ≤ s →
      (nativeFreeTailValue s b : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) := by
  exact ⟨nativeConjugatedJoint (nativeFreeBoundaryAngular b),nativeConjugatedJoint_measurable _,
    nativeConjugatedJoint_ae _,fun s hs => nativeFreeTailValue_same_dilation b
      (nativeConjugatedJoint_measurable _) (nativeConjugatedJoint_ae _) s hs⟩

#print axioms nativeFreeBoundary_shifted_coefficient
#print axioms nativeFreeTail_projected_lift
#print axioms nativeFreeTailValue_same_dilation
#print axioms exists_nativeFreeTail_same_all_scale_field
end Yamabe3.Analysis.SpherePolar
