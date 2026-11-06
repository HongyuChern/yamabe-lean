import Yamabe3.Analysis.NativeCollarVolumePairing
import Yamabe3.Analysis.NativeCollarDensityLaplacian
import Yamabe3.Analysis.NativeCollarClassicalGreen

/-! The native Green volume expression is a real continuous functional
on the same volume jet; no boundary equation is an input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

def nativeCollarGradientTest (g : RiemannianMetric 3 E) (ψ : E → ℝ) (j : Fin 3) (x : E) : ℝ :=
  ∑ i : Fin 3,partialDeriv i ψ x*nativeDivergenceMatrix g x i j

 theorem continuous_nativeCollarGradientTest (g : RiemannianMetric 3 E) {ψ : E → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (j : Fin 3) : Continuous (nativeCollarGradientTest g ψ j) := by
  apply continuous_finset_sum
  intro i _
  exact ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
    (contDiff_nativeDivergenceMatrix g i j).continuous

private theorem outside_measurable : MeasurableSet {x : E | 1<‖x‖} :=
  (isOpen_lt continuous_const continuous_norm).measurableSet

def nativeCollarGreenVolumeCLM (g : RiemannianMetric 3 E) (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) :
    NativeCollarJet →L[ℝ] ℝ :=
  (nativeCollarVolumePairCLM {x : E | 1<‖x‖} outside_measurable ψ hψ.continuous).comp
    (nativeCollarDensityLaplacianCLM g)+
    ∑ j : Fin 3,(nativeCollarVolumePairCLM {x : E | 1<‖x‖} outside_measurable
      (nativeCollarGradientTest g ψ j) (continuous_nativeCollarGradientTest g hψ j)).comp (nativeCollarJetFirstCLM j)

 theorem nativeCollarGreenVolume_eq_integral (g : RiemannianMetric 3 E) (ψ : E → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (J : NativeCollarJet) :
    nativeCollarGreenVolumeCLM g ψ hψ J=
      ∫ x in nativePoissonEntranceCollar ∩ {y : E | 1<‖y‖},
        ψ x*(nativeCollarDensityLaplacianCLM g J : E → ℝ) x+
          ∑ j : Fin 3,nativeCollarGradientTest g ψ j x*(J.2.1 j : E → ℝ) x := by
  have hi (φ : E → ℝ) (hφ : Continuous φ) (F : NativeCollarL2) :
      Integrable (fun x => φ x*(F : E → ℝ) x)
        (volume.restrict (nativePoissonEntranceCollar ∩ {y : E | 1<‖y‖})) := by
    have hφ2 : MemLp φ 2 (volume.restrict nativePoissonEntranceCollar) :=
      native_memLp_two_of_continuousOn_precompact (nativePolarTimeWindow_open (1/2)).measurableSet
        (nativePolarTimeWindow_precompact (1/2)) (nativePolarTimeWindow_closure_offZero (1/2)) hφ.continuousOn
    exact (hφ2.integrable_mul (Lp.memLp F)).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  simp only [nativeCollarGreenVolumeCLM,ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,nativeCollarVolumePair_eq_integral]
  change (∫ x in nativePoissonEntranceCollar ∩ {y : E | 1<‖y‖},ψ x*(nativeCollarDensityLaplacianCLM g J : E → ℝ) x)+
    (∑ j : Fin 3,∫ x in nativePoissonEntranceCollar ∩ {y : E | 1<‖y‖},
      nativeCollarGradientTest g ψ j x*(J.2.1 j : E → ℝ) x)=_
  rw [← integral_finsetSum _ (fun j _ => hi _ (continuous_nativeCollarGradientTest g hψ j) _),
    ← integral_add (hi ψ hψ.continuous _) (integrable_finsetSum _ (fun j _ => hi _ (continuous_nativeCollarGradientTest g hψ j) _))]

 theorem nativeCollarGreenVolume_C2 (g : RiemannianMetric 3 E) (ψ : E → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (u : nativeC2OffZero) :
    nativeCollarGreenVolumeCLM g ψ hψ (nativeC2CollarJetLinear u)=
      ∫ x in nativePoissonEntranceCollar ∩ {y : E | 1<‖y‖},nativeCollarClassicalGreenIntegrand g u.val ψ x := by
  rw [nativeCollarGreenVolume_eq_integral]
  have hμ : volume.restrict (nativePoissonEntranceCollar ∩ {y : E | 1<‖y‖})≤volume.restrict nativePoissonEntranceCollar :=
    Measure.restrict_mono inter_subset_left le_rfl
  apply integral_congr_ae
  filter_upwards [ae_mono hμ (nativeCollarDensityLaplacian_C2_ae g u),
    ae_mono hμ (eventually_all.mpr (fun j => ((nativeC2Collar_memLp u.property).2.1 j).coeFn_toLp)),
    ae_mono hμ (ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet)] with x hd hfirst hx
  rw [hd]
  have hux : ContDiffAt ℝ 2 u.val x := u.property.contDiffAt
    (isClosed_singleton.isOpen_compl.mem_nhds
      (subset_closure.trans (nativePolarTimeWindow_closure_offZero (1/2)) hx))
  have hp := native_principalSource_eq_negative_density_laplacian_C2 g g.leviCivitaData hux
  have hf (j : Fin 3) : ((nativeC2CollarJetLinear u).2.1 j : E → ℝ) x=partialDeriv j u.val x := hfirst j
  simp only [hf,nativeCollarClassicalGreenIntegrand,hp]
  have hs : (∑ j : Fin 3,nativeCollarGradientTest g ψ j x*partialDeriv j u.val x)=
      ∑ i : Fin 3,partialDeriv i ψ x*matrixFlux (nativeDivergenceMatrix g) (fun j => partialDeriv j u.val) i x := by
    simp only [nativeCollarGradientTest,matrixFlux,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  ring

#print axioms nativeCollarGreenVolume_eq_integral
#print axioms nativeCollarGreenVolume_C2
end Yamabe3.Analysis.SpherePolar
