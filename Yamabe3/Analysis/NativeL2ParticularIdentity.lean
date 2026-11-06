import Yamabe3.Analysis.NativeL2ParticularH2Collar
import Yamabe3.Analysis.NativeCollarSeriesIdentification

/-! Same-field identification: the actual H2 collar sum is the physical
lift of the high projection of the original continuous L2 particular
curve. A joint measurable representative is constructed, not assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
  (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|V (t-s)|)≤κ)
  (F : ℝ →ᵇ SpectralSpace AngularIndex) (hF : MemLp F 2)

def nativeL2ParticularCurve (t : ℝ) : AngularL2 :=
  Real.exp (-2*t) • nativeHighProjection (angularBasis.repr.symm
    (spectralIntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
      (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hminus F t))

theorem nativeL2ParticularCurve_continuous : Continuous (nativeL2ParticularCurve hκ0 hκ1 V hminus F) := by
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    (nativeHighProjection.continuous.comp (angularBasis.repr.symm.continuous.comp
      (spectralIntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
        (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hminus F).continuous))

theorem nativeL2ParticularCurve_coefficient (i : AngularIndex) (t : ℝ) :
    inner ℝ (angularBasis i) (nativeL2ParticularCurve hκ0 hκ1 V hminus F t)=
      if 6≤angularEigenvalue i then Real.exp (-2*t)*
        spectralIntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
          (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hminus F t i else 0 := by
  unfold nativeL2ParticularCurve
  rw [real_inner_smul_right,nativeHighProjection,nativeAngularProjection_coefficient,
    ←HilbertBasis.repr_apply_apply,LinearIsometryEquiv.apply_symm_apply]
  split_ifs <;> simp

theorem nativeL2ParticularCurve_finite_lift (s : Finset AngularIndex) :
    cylinderLift (projectedAngular s (nativeL2ParticularCurve hκ0 hκ1 V hminus F))=
      fun x => ∑ i ∈ s,nativeL2ParticularMode hκ0 hκ1 V hminus F i x := by
  classical
  unfold projectedAngular
  simp_rw [nativeL2ParticularCurve_coefficient]
  rw [←finitePhysical_eq_lift]
  funext x
  unfold finitePhysical
  apply Finset.sum_congr rfl
  intro i hi
  unfold nativeL2ParticularMode
  split_ifs with h
  · simp [nativeL2FiniteParticular,finitePhysical,h]
  · simp only [h,if_false,Pi.zero_apply]
    by_cases hx : x=0
    · subst x
      exact cylinderLift_zero _
    · change cylinderLift _ (⟨x,by change x≠0;exact hx⟩ : puncturedSpace)=0
      rw [cylinderLift_coe]
      simp [puncturedCylinderLift,separableCylinder]

theorem nativeL2ParticularCollarValue_eq_lift {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume]
      (nativeL2ParticularCurve hκ0 hκ1 V hminus F t : S → ℝ)) :
    (nativeL2ParticularCollarValue hκ0 hκ1 V hminus hplus F hF : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      cylinderLift w :=
  nativeCollarSeries_eq_lift _ _
    (nativeL2ParticularCollar_modes_summable hκ0 hκ1 V hminus hplus F hF).1 _
    (nativeL2ParticularCurve_continuous hκ0 hκ1 V hminus F)
    (nativeL2ParticularCurve_finite_lift hκ0 hκ1 V hminus F) hw hae

theorem exists_nativeL2Particular_same_curve_H2_collar :
    ∃ w : ℝ × S → ℝ,StronglyMeasurable w ∧
      (∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume] (nativeL2ParticularCurve hκ0 hκ1 V hminus F t : S → ℝ)) ∧
      (nativeL2ParticularCollarValue hκ0 hκ1 V hminus hplus F hF : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        cylinderLift w ∧
      MemWkp 2 2 (nativeL2ParticularCollarValue hκ0 hκ1 V hminus hplus F hF) nativePoissonEntranceCollar ∧
      (∀ j,HasWeakPartialDeriv j (nativeL2ParticularCollarFirst hκ0 hκ1 V hminus hplus F hF j)
        (nativeL2ParticularCollarValue hκ0 hκ1 V hminus hplus F hF) nativePoissonEntranceCollar) ∧
      (∀ k j,HasWeakPartialDeriv k (nativeL2ParticularCollarSecond hκ0 hκ1 V hminus hplus F hF k j)
        (nativeL2ParticularCollarFirst hκ0 hκ1 V hminus hplus F hF j) nativePoissonEntranceCollar) := by
  obtain ⟨w,hw,hae⟩ := exists_joint_L2_representative_of_continuous (nativeL2ParticularCurve_continuous hκ0 hκ1 V hminus F)
  have hae' : ∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume] (nativeL2ParticularCurve hκ0 hκ1 V hminus F t : S → ℝ) := by
    intro t
    simpa only [Measure.restrict_univ] using hae t
  have h := nativeL2ParticularCollar_H2_and_jets hκ0 hκ1 V hminus hplus F hF
  exact ⟨w,hw,hae',nativeL2ParticularCollarValue_eq_lift hκ0 hκ1 V hminus hplus F hF hw.measurable hae',h⟩

#print axioms nativeL2ParticularCurve_coefficient
#print axioms nativeL2ParticularCurve_finite_lift
#print axioms nativeL2ParticularCollarValue_eq_lift
#print axioms exists_nativeL2Particular_same_curve_H2_collar
end Yamabe3.Analysis.SpherePolar
