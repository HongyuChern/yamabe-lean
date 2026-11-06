import Yamabe3.Analysis.NativeLowReverseL2FiniteEquation
import Yamabe3.Analysis.NativeCollarLocalMultiplier
import Yamabe3.Analysis.L2TimeReflection

/-! The reversed low producer satisfies its actual physical equation for
all L2 sources. The bounded collar source map retains reflection and the
exact inverse fourth radial power. Density is used only after the C2
identity and actual second weak jet representatives have been proved. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeInverseFourthPower_continuousOn :
    ContinuousOn (fun x : E => (‖x‖^4)⁻¹) {x | x≠0} :=
  (continuous_norm.pow 4).continuousOn.inv₀ (fun x hx => pow_ne_zero 4 (norm_ne_zero_iff.mpr hx))

def nativeInverseFourthPowerCollarCLM : NativeCollarL2 →L[ℝ] NativeCollarL2 :=
  nativeCollarLocalMulCLM (fun x => (‖x‖^4)⁻¹) nativeInverseFourthPower_continuousOn

def nativeLowReverseL2SourceCLM : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] NativeCollarL2 :=
  nativeInverseFourthPowerCollarCLM.comp (nativeL2LowPhysicalSourceCLM.comp (l2TimeReflectCLM AngularSpectralSpace))

theorem nativeLowReverseL2Source_ae (F : ℝ →ᵇ AngularSpectralSpace) (hF : MemLp F 2) :
    (nativeLowReverseL2SourceCLM (hF.toLp F) : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => (‖x‖^4)⁻¹*cylinderLift (finiteAngular nativeLowIndexFinset (fun i t => F (-t) i)) x) := by
  let w := finiteAngular nativeLowIndexFinset (fun i t => F (-t) i)
  have hw : Continuous w := by
    apply continuous_finset_sum
    intro i _
    exact (((lp.evalCLM ℝ (fun _ : AngularIndex => ℝ) 2 i).continuous.comp F.continuous).comp
      continuous_fst.neg).mul ((smooth_angularRepresentative i).continuous.comp continuous_snd)
  have hr := nativeL2LowPhysicalSource_eq_lift (l2TimeReflectCLM AngularSpectralSpace (hF.toLp F)) hw.measurable (by
    have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hF.coeFn_toLp
    filter_upwards [l2TimeReflect_ae AngularSpectralSpace (hF.toLp F),hn] with t ht hn
    rw [ht,hn]
    exact nativeLowL2_finite_source_ae F (-t))
  exact (nativeCollarLocalMulCLM_ae (fun x => (‖x‖^4)⁻¹) nativeInverseFourthPower_continuousOn _).trans (by
    filter_upwards [hr] with x hx
    exact congrArg (fun a => (‖x‖^4)⁻¹*a) hx)

variable (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)

def nativeLowReverseL2PhysicalOperatorCLM : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] NativeCollarL2 :=
  ((∑ j : Fin 3,nativeCollarJetSecondCLM j j)+
    (nativeCollarPotentialMulCLM (nativeLowReversePotential v hv hb)).comp nativeCollarJetValueCLM).comp
      (nativeLowReverseL2RawJetCLM v hv hb)

theorem nativeLowReverseL2_physical_equation_continuous (F : continuousL2Source AngularSpectralSpace) :
    nativeLowReverseL2PhysicalOperatorCLM v hv hb (continuousL2SourceInclusion _ F)=
      nativeLowReverseL2SourceCLM (continuousL2SourceInclusion _ F) := by
  let u := nativeLowReverseL2PhysicalField v hv hb (continuousL2SourceInclusion _ F)
  have hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E) := (nativeLowReverseL2Physical_collar_energy v hv hb F.val F.property).1
  let V := nativeLowReversePotential v hv hb
  let L := ∑ j : Fin 3,nativeC2CollarSecond hu j j
  let U := nativeC2CollarValue hu
  have hval : (U : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] u := (nativeC2Collar_memLp hu).1.coeFn_toLp
  have hs : ∀ᵐ x ∂volume.restrict nativePoissonEntranceCollar,∀ j : Fin 3,
      nativeC2CollarSecond hu j j x=nativeCoordinateSecond j j u x :=
    ae_all_iff.mpr (fun j => ((nativeC2Collar_memLp hu).2.2 j j).coeFn_toLp)
  have hL : (L : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] nativeCoordinateLaplacian u := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => nativeC2CollarSecond hu j j),hs] with x hx hs
    change L x=_
    rw [hx]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => hs j)
  unfold nativeLowReverseL2PhysicalOperatorCLM
  simp only [ContinuousLinearMap.comp_apply,nativeLowReverseL2RawJet_agrees_continuous,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply]
  change L+nativeCollarPotentialMulCLM V U=nativeLowReverseL2SourceCLM (continuousL2SourceInclusion _ F)
  apply Lp.ext
  filter_upwards [Lp.coeFn_add L (nativeCollarPotentialMulCLM V U),hL,hval,
    nativeCollarPotentialMulCLM_ae V U,nativeLowReverseL2Source_ae F.val F.property,
    ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x ha hL hu hV hr hx
  rw [ha]
  change L x+nativeCollarPotentialMulCLM V U x=_
  change nativeLowReverseL2SourceCLM (continuousL2SourceInclusion _ F) x=
    (‖x‖^4)⁻¹*cylinderLift (finiteAngular nativeLowIndexFinset (fun i t => F.val (-t) i)) x at hr
  rw [hL,hV,hu,hr]
  exact nativeLowReverseL2_finite_physical_equation v hv hb F.val F.property
    (cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx))

theorem nativeLowReverseL2PhysicalOperatorCLM_eq_source :
    nativeLowReverseL2PhysicalOperatorCLM v hv hb=nativeLowReverseL2SourceCLM := by
  apply ContinuousLinearMap.ext
  intro F
  have hc := isClosed_eq (nativeLowReverseL2PhysicalOperatorCLM v hv hb).continuous nativeLowReverseL2SourceCLM.continuous
  exact (continuousL2SourceInclusion_dense AngularSpectralSpace).induction_on F hc
    (nativeLowReverseL2_physical_equation_continuous v hv hb)

theorem nativeLowReverseL2_physical_equation (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    (∑j : Fin 3,(nativeLowReverseL2RawJetCLM v hv hb F).2.2 j j)+
      nativeCollarPotentialMulCLM (nativeLowReversePotential v hv hb) (nativeLowReverseL2RawJetCLM v hv hb F).1=
        nativeLowReverseL2SourceCLM F := by
  have h := DFunLike.congr_fun (nativeLowReverseL2PhysicalOperatorCLM_eq_source v hv hb) F
  simpa only [nativeLowReverseL2PhysicalOperatorCLM,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
    nativeCollarJetSecondCLM,nativeCollarJetValueCLM,ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd'] using h

#print axioms nativeInverseFourthPower_continuousOn
#print axioms nativeLowReverseL2Source_ae
#print axioms nativeLowReverseL2_physical_equation_continuous
#print axioms nativeLowReverseL2PhysicalOperatorCLM_eq_source
#print axioms nativeLowReverseL2_physical_equation
end Yamabe3.Analysis.SpherePolar
