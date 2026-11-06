import Yamabe3.Analysis.NativeCollarClassicalFirstGreen
import Yamabe3.Analysis.NativeCollarVolumePairing
import Yamabe3.Analysis.NativeCollarNativeBoundaryPairing
import Yamabe3.Analysis.NativeCollarJetWeakDerivatives

/-! Continuous first-order Green identity on actual strong H2 jets. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

theorem native_partial_test_continuous {ψ : E → ℝ} (hψ : ContDiff ℝ 2 ψ) (j : Fin 3) :
    Continuous (partialDeriv j ψ) :=
  (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const

def nativeCollarFirstGreenRegionCLM (s : Set E) (hs : MeasurableSet s)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (j : Fin 3) : NativeCollarJet →L[ℝ] ℝ :=
  (nativeCollarVolumePairCLM s hs (partialDeriv j ψ) (native_partial_test_continuous hψ j)).comp nativeCollarJetValueCLM+
    (nativeCollarVolumePairCLM s hs ψ hψ.continuous).comp (nativeCollarJetFirstCLM j)

def nativeCollarValueNormalPairCLM (ψ : E → ℝ) (hψ : Continuous ψ) (j : Fin 3) :
    nativeCollarJetClosure →L[ℝ] ℝ :=
  (innerSL ℝ (nativeSphereWeightedTest (RiemannianMetric.euclideanMetric 3)
    (fun x : E => ψ x*x j) (hψ.mul (show E →L[ℝ] ℝ from EuclideanSpace.proj j).continuous))).comp nativeCollarValueTraceCLM

theorem nativeCollarFirstGreenRegion_eq_integral (s : Set E) (hs : MeasurableSet s)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (j : Fin 3) (J : NativeCollarJet) :
    nativeCollarFirstGreenRegionCLM s hs ψ hψ j J=
      ∫x in nativePoissonEntranceCollar ∩ s,
        partialDeriv j ψ x*(J.1 : E → ℝ) x+ψ x*(J.2.1 j : E → ℝ) x := by
  have hi (φ : E → ℝ) (hφ : Continuous φ) (F : NativeCollarL2) :
      Integrable (fun x => φ x*(F : E → ℝ) x) (volume.restrict (nativePoissonEntranceCollar ∩ s)) := by
    have hm : MemLp φ 2 (volume.restrict nativePoissonEntranceCollar) :=
      native_memLp_two_of_continuousOn_precompact (nativePolarTimeWindow_open (1/2)).measurableSet
        (nativePolarTimeWindow_precompact (1/2)) (nativePolarTimeWindow_closure_offZero (1/2)) hφ.continuousOn
    exact (hm.integrable_mul (Lp.memLp F)).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  simp only [nativeCollarFirstGreenRegionCLM,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    nativeCollarVolumePair_eq_integral]
  exact (integral_add (hi _ (native_partial_test_continuous hψ j) _) (hi _ hψ.continuous _)).symm

theorem nativeCollarFirstGreenRegion_C2 (s : Set E) (hs : MeasurableSet s)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (j : Fin 3) (u : nativeC2OffZero) :
    nativeCollarFirstGreenRegionCLM s hs ψ hψ j (nativeC2CollarJetLinear u)=
      ∫x in nativePoissonEntranceCollar ∩ s,nativeCollarFirstGreenIntegrand j u.val ψ x := by
  rw [nativeCollarFirstGreenRegion_eq_integral]
  have hμ : volume.restrict (nativePoissonEntranceCollar ∩ s)≤volume.restrict nativePoissonEntranceCollar :=
    Measure.restrict_mono inter_subset_left le_rfl
  apply integral_congr_ae
  filter_upwards [ae_mono hμ (nativeC2Collar_memLp u.property).1.coeFn_toLp,
    ae_mono hμ ((nativeC2Collar_memLp u.property).2.1 j).coeFn_toLp] with x hu hd
  change partialDeriv j ψ x*((nativeC2CollarJetLinear u).1 : E → ℝ) x+
    ψ x*((nativeC2CollarJetLinear u).2.1 j : E → ℝ) x=_
  have hu' : ((nativeC2CollarJetLinear u).1 : E → ℝ) x=u.val x := hu
  have hd' : ((nativeC2CollarJetLinear u).2.1 j : E → ℝ) x=partialDeriv j u.val x := hd
  simp only [hu',hd',nativeCollarFirstGreenIntegrand]

theorem nativeCollarValueNormalPair_C2 (ψ : E → ℝ) (hψ : Continuous ψ) (j : Fin 3) (u : nativeC2OffZero) :
    nativeCollarValueNormalPairCLM ψ hψ j (nativeC2CollarJetInclusion u)=
      ∫θ : S,ψ (θ:E)*u.val (θ:E)*(θ:E) j ∂angularVolume := by
  change inner ℝ (nativeSphereWeightedTest (RiemannianMetric.euclideanMetric 3) _ _)
    (nativeCollarValueTraceCLM (nativeC2CollarJetInclusion u))=_
  rw [(nativeCollarTraceCLM_agrees_C2 u).1,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [nativeSphereWeightedTest_ae (RiemannianMetric.euclideanMetric 3)
    (fun x : E => ψ x*x j) (hψ.mul (show E →L[ℝ] ℝ from EuclideanSpace.proj j).continuous),
    (native_C1_sphere_restriction_memLp u.property.continuousOn).coeFn_toLp] with θ hψ hu
  have hu' : (nativeC2ValueTraceLinear u : S → ℝ) θ=u.val (θ:E) := hu
  simp only [RCLike.inner_apply,conj_trivial,hψ,hu',nativeEuclidean_density,one_mul]
  ring

theorem nativeCollarWeakFirstGreen_exterior (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆nativePoissonEntranceCollar)
    (j : Fin 3) (J : nativeCollarJetClosure) :
    nativeCollarFirstGreenRegionCLM {x : E | 1<‖x‖} (isOpen_lt continuous_const continuous_norm).measurableSet ψ hψ j J.val=
      -nativeCollarValueNormalPairCLM ψ hψ.continuous j J := by
  have he : (fun J : nativeCollarJetClosure => nativeCollarFirstGreenRegionCLM {x : E | 1<‖x‖}
        (isOpen_lt continuous_const continuous_norm).measurableSet ψ hψ j J.val)=
      (fun J : nativeCollarJetClosure => -nativeCollarValueNormalPairCLM ψ hψ.continuous j J) := by
    apply nativeC2CollarJetInclusion_dense.equalizer
      ((nativeCollarFirstGreenRegionCLM _ _ ψ hψ j).continuous.comp continuous_subtype_val)
      (nativeCollarValueNormalPairCLM ψ hψ.continuous j).continuous.neg
    funext u
    change nativeCollarFirstGreenRegionCLM _ _ ψ hψ j (nativeC2CollarJetLinear u)=
      -nativeCollarValueNormalPairCLM ψ hψ.continuous j (nativeC2CollarJetInclusion u)
    rw [nativeCollarFirstGreenRegion_C2,native_collar_classical_first_green u ψ hψ hc hs j,
      nativeCollarValueNormalPair_C2]
  exact congrFun he J

#print axioms native_partial_test_continuous
#print axioms nativeCollarFirstGreenRegion_eq_integral
#print axioms nativeCollarFirstGreenRegion_C2
#print axioms nativeCollarValueNormalPair_C2
#print axioms nativeCollarWeakFirstGreen_exterior
end Yamabe3.Analysis.SpherePolar
