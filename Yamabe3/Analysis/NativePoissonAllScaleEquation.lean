import Yamabe3.Analysis.NativeShiftedEntranceAnyScale
import Yamabe3.Analysis.NativePoissonPositiveCollarEquation
import Yamabe3.Analysis.NativeC2CollarSeriesEquation

/-! The original Poisson field satisfies its equation on every shifted
positive-time collar. The auxiliary finite-mode convergence is used only
to identify the equation, not as a uniform tail bound. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

def nativePositiveScaledCollar (s : ℝ) : Set E :=
  nativePoissonEntranceCollar ∩ Metric.ball 0 (Real.exp s)

theorem nativePositiveScaledCollar_open (s : ℝ) : IsOpen (nativePositiveScaledCollar s) :=
  (nativePolarTimeWindow_open (1/2)).inter Metric.isOpen_ball

def nativePositiveScaledRestrictionCLM (s : ℝ) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) →L[ℝ] Lp ℝ 2 (volume.restrict (nativePositiveScaledCollar s)) :=
  nativeCollarSubsetRestrictionCLM _ inter_subset_left

theorem nativeShiftedEntranceCoefficient_homogeneous (P : NativeHighPotential) (b : AngularH1)
    (s : ℝ) (i : AngularIndex) (t : ℝ) (ht : 0 ≤ t+s) :
    finiteTimeLaplacian (nativeShiftedEntranceCoefficient P b s) i t=
      -(boundedTimeTranslate ℝ s P.potential) t*nativeShiftedEntranceCoefficient P b s i t := by
  have h := nativePoissonEntranceExtension_homogeneous P b i (t+s) ht
  unfold finiteTimeLaplacian at h ⊢
  unfold nativeShiftedEntranceCoefficient
  rw [weightedTimeShift_second s (P.entranceExtension_C2 b i)]
  change Real.exp (2*s)*deriv (deriv (nativePoissonEntranceExtension P b i)) (t+s)-
      (angularEigenvalue i+1/4)*(Real.exp (2*s)*nativePoissonEntranceExtension P b i (t+s))=
        -P.potential (t+s)*(Real.exp (2*s)*nativePoissonEntranceExtension P b i (t+s))
  have he := congrArg (fun a : ℝ => Real.exp (2*s)*a) h
  nlinarith only [he]

theorem nativeShiftedEntranceFinite_homogeneous (P : NativeHighPotential) (b : AngularH1)
    (s : ℝ) (m : Finset AngularIndex) {x : E} (hx : x ∈ nativePositiveScaledCollar s) :
    nativeCoordinateLaplacian (finitePhysical m (nativeShiftedEntranceCoefficient P b s)) x+
      nativeHalfEndPotentialCoefficient (boundedTimeTranslate ℝ s P.potential) x*
        finitePhysical m (nativeShiftedEntranceCoefficient P b s) x=0 := by
  have hx0 := cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx.1)
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have ht : 0 ≤ -Real.log ‖x‖+s := by
    have hr : ‖x‖ < Real.exp s := by simpa only [Metric.mem_ball,dist_zero_right] using hx.2
    have hl := Real.log_le_log hn hr.le
    rw [Real.log_exp] at hl
    linarith
  let y : puncturedSpace := ⟨x,by change x ≠ 0;exact hx0⟩
  rw [native_finitePhysical_laplacian m _ (fun i _ => nativeShiftedEntranceCoefficient_C2 P b s i) hx0,finitePhysical_eq_lift]
  change cylinderLift (finiteAngular m (finiteTimeLaplacian (nativeShiftedEntranceCoefficient P b s))) (y:E)/‖x‖^2+
    nativeHalfEndPotentialCoefficient (boundedTimeTranslate ℝ s P.potential) x*
      cylinderLift (finiteAngular m (nativeShiftedEntranceCoefficient P b s)) (y:E)=0
  rw [cylinderLift_coe,cylinderLift_coe]
  change radialScale ‖x‖*(∑ i ∈ m,finiteTimeLaplacian (nativeShiftedEntranceCoefficient P b s) i (-Real.log ‖x‖)*
    angularRepresentative i (cylinderCoordinates y).2)/‖x‖^2+
    ((boundedTimeTranslate ℝ s P.potential) (-Real.log ‖x‖)/‖x‖^2)*
      (radialScale ‖x‖*(∑ i ∈ m,nativeShiftedEntranceCoefficient P b s i (-Real.log ‖x‖)*
        angularRepresentative i (cylinderCoordinates y).2))=0
  simp_rw [nativeShiftedEntranceCoefficient_homogeneous P b s _ _ ht,mul_assoc]
  rw [←Finset.mul_sum]
  ring

theorem nativeShiftedEntrance_homogeneous (P : NativeHighPotential) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) (s : ℝ) :
    nativePositiveScaledRestrictionCLM s ((∑ j : Fin 3,nativeShiftedEntranceSecond P s b j j)+
      nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s P.potential) (nativeShiftedEntranceValue P s b))=0 := by
  have h := nativeShiftedEntrance_any_scale_summable P s b hb
  exact nativeC2CollarSeries_equation_zero _ inter_subset_left (nativePositiveScaledCollar_open s).measurableSet
    (boundedTimeTranslate ℝ s P.potential) (fun i => ⟨_,nativeShiftedEntranceMode_C2 P s b i⟩)
    h.1 h.2.2 (fun i x hx => nativeShiftedEntranceFinite_homogeneous P b s {i} hx)

variable (P : NativeHighPotential)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)

theorem nativePoissonAllScale_eq_shifted (s : ℝ) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    nativePoissonAllScaleValue P hplus s b=nativeShiftedEntranceValue P s b ∧
    (∀ j,nativePoissonAllScaleFirst P hplus s b j=nativeShiftedEntranceFirst P s b j) ∧
    (∀ k j,nativePoissonAllScaleSecond P hplus s b k j=nativeShiftedEntranceSecond P s b k j) := by
  obtain ⟨w,hw,hae,_⟩ := nativePoissonReflectedCurve_joint_representative P b
  have hv : nativePoissonAllScaleValue P hplus s b=nativeShiftedEntranceValue P s b := by
    apply Lp.ext
    exact (nativePoissonAllScaleValue_same_field P hplus b hb hw.measurable hae s).trans
      (nativeShiftedEntranceValue_any_scale_same_field P s b hb hw.measurable hae).symm
  have hn := nativePoissonAllScale_H2_same_jets P hplus s b hb
  have ho := nativeShiftedEntrance_any_scale_H2_same_jets P s b hb
  have h1 (j : Fin 3) : nativePoissonAllScaleFirst P hplus s b j=nativeShiftedEntranceFirst P s b j := by
    apply Lp.ext
    have h := hn.2.1 j
    rw [hv] at h
    exact h.ae_eq (nativePolarTimeWindow_open (1/2)) (ho.2.1 j)
      ((Lp.memLp _).locallyIntegrable (by norm_num)) ((Lp.memLp _).locallyIntegrable (by norm_num))
  refine ⟨hv,h1,fun k j => ?_⟩
  apply Lp.ext
  have h := hn.2.2 k j
  rw [h1 j] at h
  exact h.ae_eq (nativePolarTimeWindow_open (1/2)) (ho.2.2 k j)
    ((Lp.memLp _).locallyIntegrable (by norm_num)) ((Lp.memLp _).locallyIntegrable (by norm_num))

theorem nativePoissonAllScale_homogeneous (s : ℝ) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    nativePositiveScaledRestrictionCLM s ((∑ j : Fin 3,nativePoissonAllScaleSecond P hplus s b j j)+
      nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s P.potential) (nativePoissonAllScaleValue P hplus s b))=0 := by
  have h := nativePoissonAllScale_eq_shifted P hplus s b hb
  simp_rw [h.1,h.2.2]
  exact nativeShiftedEntrance_homogeneous P b hb s

#print axioms nativeShiftedEntranceCoefficient_homogeneous
#print axioms nativeShiftedEntranceFinite_homogeneous
#print axioms nativeShiftedEntrance_homogeneous
#print axioms nativePoissonAllScale_eq_shifted
#print axioms nativePoissonAllScale_homogeneous
end Yamabe3.Analysis.SpherePolar
