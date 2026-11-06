import Yamabe3.Analysis.NativeLowL2FiniteEquation

/-! Equality of the actual second weak jets plus the model potential
with the same low source, on all L2 inputs. Density extends a proved C2
physical equation; it is not an assumed distributional interface. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0 ≤ v t ∧ v t ≤ 1)

def nativeLowL2PhysicalOperatorCLM : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] NativeCollarL2 :=
  ((∑ j : Fin 3,nativeCollarJetSecondCLM j j)+
    (nativeCollarPotentialMulCLM (delaunayPhasePotentialBCF v hv hb 0)).comp nativeCollarJetValueCLM).comp
      (nativeLowL2RawJetCLM v hv hb)

theorem nativeLowL2_physical_equation_continuous (F : continuousL2Source AngularSpectralSpace) :
    nativeLowL2PhysicalOperatorCLM v hv hb (continuousL2SourceInclusion _ F)=
      nativeL2LowPhysicalSourceCLM (continuousL2SourceInclusion _ F) := by
  let u := nativeLowL2PhysicalField v hv hb (continuousL2SourceInclusion _ F)
  have hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E) := (nativeLowL2Physical_collar_energy v hv hb F.val F.property).1
  let V := delaunayPhasePotentialBCF v hv hb 0
  let L := ∑ j : Fin 3,nativeC2CollarSecond hu j j
  let U := nativeC2CollarValue hu
  let w := finiteAngular nativeLowIndexFinset (fun i t => F.val t i)
  have hw : Continuous w := by
    apply continuous_finset_sum
    intro i _
    exact (((lp.evalCLM ℝ (fun _ : AngularIndex => ℝ) 2 i).continuous.comp F.val.continuous).comp
      continuous_fst).mul ((smooth_angularRepresentative i).continuous.comp continuous_snd)
  have hr := nativeL2LowPhysicalSource_eq_lift (continuousL2SourceInclusion _ F) hw.measurable (by
    filter_upwards [F.property.coeFn_toLp] with t ht
    change (F.property.toLp F.val) t=F.val t at ht
    change (fun θ => w (t,θ))=ᵐ[angularVolume]
      (nativeLowProjection (angularBasis.repr.symm ((F.property.toLp F.val) t)) : S → ℝ)
    rw [ht]
    exact nativeLowL2_finite_source_ae F.val t)
  have hval : (U : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]u := (nativeC2Collar_memLp hu).1.coeFn_toLp
  have hs : ∀ᵐ x ∂volume.restrict nativePoissonEntranceCollar,∀ j : Fin 3,
      nativeC2CollarSecond hu j j x=nativeCoordinateSecond j j u x :=
    ae_all_iff.mpr (fun j => ((nativeC2Collar_memLp hu).2.2 j j).coeFn_toLp)
  have hL : (L : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] nativeCoordinateLaplacian u := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => nativeC2CollarSecond hu j j),hs] with x hx hs
    change L x=_
    rw [hx]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => hs j)
  unfold nativeLowL2PhysicalOperatorCLM
  simp only [ContinuousLinearMap.comp_apply,nativeLowL2RawJet_agrees_continuous,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply]
  change L+nativeCollarPotentialMulCLM V U=nativeL2LowPhysicalSourceCLM (continuousL2SourceInclusion _ F)
  apply Lp.ext
  filter_upwards [Lp.coeFn_add L (nativeCollarPotentialMulCLM V U),hL,hval,
    nativeCollarPotentialMulCLM_ae V U,hr,
    ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x ha hL hu hV hr hx
  rw [ha]
  change L x+nativeCollarPotentialMulCLM V U x=_
  rw [hL,hV,hu,hr]
  exact nativeLowL2_finite_physical_equation v hv hb F.val F.property
    (cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx))

theorem nativeLowL2PhysicalOperatorCLM_eq_source :
    nativeLowL2PhysicalOperatorCLM v hv hb=nativeL2LowPhysicalSourceCLM := by
  apply ContinuousLinearMap.ext
  intro F
  have hc := isClosed_eq (nativeLowL2PhysicalOperatorCLM v hv hb).continuous nativeL2LowPhysicalSourceCLM.continuous
  exact (continuousL2SourceInclusion_dense AngularSpectralSpace).induction_on F hc
    (nativeLowL2_physical_equation_continuous v hv hb)

theorem nativeLowL2_physical_equation (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    (∑ j : Fin 3,(nativeLowL2RawJetCLM v hv hb F).2.2 j j)+
      nativeCollarPotentialMulCLM (delaunayPhasePotentialBCF v hv hb 0) (nativeLowL2RawJetCLM v hv hb F).1=
        nativeL2LowPhysicalSourceCLM F := by
  have h := DFunLike.congr_fun (nativeLowL2PhysicalOperatorCLM_eq_source v hv hb) F
  simpa only [nativeLowL2PhysicalOperatorCLM,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
    nativeCollarJetSecondCLM,nativeCollarJetValueCLM,ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd'] using h

#print axioms nativeLowL2_physical_equation_continuous
#print axioms nativeLowL2PhysicalOperatorCLM_eq_source
#print axioms nativeLowL2_physical_equation
end Yamabe3.Analysis.SpherePolar
