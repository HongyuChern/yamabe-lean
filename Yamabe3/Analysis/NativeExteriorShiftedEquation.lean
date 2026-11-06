import Yamabe3.Analysis.NativeExteriorAllScaleField
import Yamabe3.Analysis.NativePoissonExteriorCollarEquation
import Yamabe3.Analysis.NativeC2CollarSeriesEquation
import Yamabe3.Analysis.NativeOrbitCollarJacobian

/-! Actual homogeneous equation of the same exterior Poisson field on
each shifted exterior portion of a collar. The artificial positive-time
extension is excluded explicitly. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

def nativeNegativeScaledCollar (s : ℝ) : Set E :=
  nativePoissonEntranceCollar ∩ {x | Real.exp s<‖x‖}

theorem nativeNegativeScaledCollar_open (s : ℝ) : IsOpen (nativeNegativeScaledCollar s) :=
  (nativePolarTimeWindow_open (1/2)).inter (isOpen_lt continuous_const continuous_norm)

def nativeNegativeScaledRestrictionCLM (s : ℝ) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) →L[ℝ] Lp ℝ 2 (volume.restrict (nativeNegativeScaledCollar s)) :=
  nativeCollarSubsetRestrictionCLM _ inter_subset_left

theorem nativeExteriorShiftedCoefficient_homogeneous (P : NativeHighPotential) (b : AngularH1)
    (s : ℝ) (i : AngularIndex) (t : ℝ) (ht : t+s≤0) :
    finiteTimeLaplacian (nativeExteriorShiftedCoefficient P b s) i t=
      -(boundedTimeTranslate ℝ s (nativePoissonExteriorPotential P)) t*nativeExteriorShiftedCoefficient P b s i t := by
  have h := nativePoissonExteriorExtension_homogeneous P b i (t+s) ht
  unfold finiteTimeLaplacian at h ⊢
  unfold nativeExteriorShiftedCoefficient
  rw [weightedTimeShift_second s (P.exteriorExtension_C2 b i)]
  change Real.exp (2*s)*deriv (deriv (nativePoissonExteriorExtension P b i)) (t+s)-
      (angularEigenvalue i+1/4)*(Real.exp (2*s)*nativePoissonExteriorExtension P b i (t+s))=
        -P.potential (-(t+s))*(Real.exp (2*s)*nativePoissonExteriorExtension P b i (t+s))
  change deriv (deriv (nativePoissonExteriorExtension P b i)) (t+s)-(angularEigenvalue i+1/4)*nativePoissonExteriorExtension P b i (t+s)= -P.potential (-(t+s))*nativePoissonExteriorExtension P b i (t+s) at h
  have he := congrArg (fun a : ℝ => Real.exp (2*s)*a) h
  nlinarith only [he]

theorem nativeExteriorShiftedFinite_homogeneous (P : NativeHighPotential) (b : AngularH1)
    (s : ℝ) (m : Finset AngularIndex) {x : E} (hx : x ∈ nativeNegativeScaledCollar s) :
    nativeCoordinateLaplacian (finitePhysical m (nativeExteriorShiftedCoefficient P b s)) x+
      nativeHalfEndPotentialCoefficient (boundedTimeTranslate ℝ s (nativePoissonExteriorPotential P)) x*
        finitePhysical m (nativeExteriorShiftedCoefficient P b s) x=0 := by
  have hx0 := cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx.1)
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have ht : -Real.log ‖x‖+s≤0 := by
    have hl := Real.log_le_log (Real.exp_pos s) hx.2.le
    rw [Real.log_exp] at hl
    linarith
  let y : puncturedSpace := ⟨x,by change x ≠ 0;exact hx0⟩
  rw [native_finitePhysical_laplacian m _ (fun i _ => nativeExteriorShiftedCoefficient_C2 P b s i) hx0,finitePhysical_eq_lift]
  change cylinderLift (finiteAngular m (finiteTimeLaplacian (nativeExteriorShiftedCoefficient P b s))) (y:E)/‖x‖^2+
    nativeHalfEndPotentialCoefficient (boundedTimeTranslate ℝ s (nativePoissonExteriorPotential P)) x*
      cylinderLift (finiteAngular m (nativeExteriorShiftedCoefficient P b s)) (y:E)=0
  rw [cylinderLift_coe,cylinderLift_coe]
  change radialScale ‖x‖*(∑ i ∈ m,finiteTimeLaplacian (nativeExteriorShiftedCoefficient P b s) i (-Real.log ‖x‖)*
    angularRepresentative i (cylinderCoordinates y).2)/‖x‖^2+
    ((boundedTimeTranslate ℝ s (nativePoissonExteriorPotential P)) (-Real.log ‖x‖)/‖x‖^2)*
      (radialScale ‖x‖*(∑ i ∈ m,nativeExteriorShiftedCoefficient P b s i (-Real.log ‖x‖)*
        angularRepresentative i (cylinderCoordinates y).2))=0
  simp_rw [nativeExteriorShiftedCoefficient_homogeneous P b s _ _ ht,mul_assoc]
  rw [←Finset.mul_sum]
  ring

theorem nativeExteriorShifted_homogeneous (P : NativeHighPotential) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) (s : ℝ) :
    nativeNegativeScaledRestrictionCLM s ((∑ j : Fin 3,nativeExteriorShiftedSecond P s b j j)+
      nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s (nativePoissonExteriorPotential P)) (nativeExteriorShiftedValue P s b))=0 := by
  have h := nativeExteriorShifted_summable P s b hb
  exact nativeC2CollarSeries_equation_zero _ inter_subset_left (nativeNegativeScaledCollar_open s).measurableSet
    (boundedTimeTranslate ℝ s (nativePoissonExteriorPotential P)) (fun i => ⟨_,nativeExteriorShiftedMode_C2 P s b i⟩)
    h.1 h.2.2 (fun i x hx => nativeExteriorShiftedFinite_homogeneous P b s {i} hx)

theorem nativeExteriorShifted_flat_equation (P : NativeHighPotential) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) (s : ℝ) :
    nativeNegativeScaledRestrictionCLM s
      (nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s (nativePoissonExteriorPotential P))
        (nativeExteriorShiftedJet P s b hb).val)=0 := by
  change nativeNegativeScaledRestrictionCLM s
    (-((∑j : Fin 3,nativeExteriorShiftedSecond P s b j j)+
      nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s (nativePoissonExteriorPotential P)) (nativeExteriorShiftedValue P s b)))=0
  rw [map_neg,nativeExteriorShifted_homogeneous P b hb s,neg_zero]

#print axioms nativeExteriorShiftedCoefficient_homogeneous
#print axioms nativeExteriorShiftedFinite_homogeneous
#print axioms nativeExteriorShifted_homogeneous
#print axioms nativeExteriorShifted_flat_equation
end Yamabe3.Analysis.SpherePolar
