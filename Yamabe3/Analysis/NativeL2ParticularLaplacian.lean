import Yamabe3.Analysis.NativeL2PhysicalSource
import Yamabe3.Analysis.NativeC2CollarLaplacianSeries
import Yamabe3.Analysis.NativeL2ParticularExtension

/-! Actual all-L2 physical Laplacian of the same H2 particular field.
Finite C2 equations identify the strong diagonal weak-jet sum on dense
continuous sources, then equality of continuous operators extends it to
all L2 sources. The residual retains F - V U with the same U. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
  (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|V (t-s)|)≤κ)

theorem nativeL2Particular_laplacian_continuous
    (F : ℝ →ᵇ SpectralSpace AngularIndex) (hF : MemLp F 2) :
    (∑ j : Fin 3,nativeL2ParticularCollarSecond hκ0 hκ1 V hminus hplus F hF j j)=
      nativeL2HighPhysicalSourceCLM (nativeL2ResidualCLM V (hF.toLp F)) := by
  obtain ⟨w,hw,hae⟩ := exists_joint_L2_representative_of_continuous
    (nativeL2ParticularResidualCurve_continuous hκ0 hκ1 V hminus F)
  have hae' : ∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume]
      (nativeL2ParticularResidualCurve hκ0 hκ1 V hminus F t : S → ℝ) := by
    intro t
    simpa only [Measure.restrict_univ] using hae t
  have hleft := nativeC2Collar_series_laplacian_eq_lift
    (nativeL2ParticularMode hκ0 hκ1 V hminus F)
    (nativeL2ParticularMode_C2 hκ0 hκ1 V hminus hplus F hF)
    (fun j => (nativeL2ParticularCollar_modes_summable hκ0 hκ1 V hminus hplus F hF).2.2 j j)
    _ (nativeL2ParticularResidualCurve_continuous hκ0 hκ1 V hminus F)
    (nativeL2Particular_finite_laplacian hκ0 hκ1 V hminus F) hw.measurable hae'
  have hright := nativeL2HighPhysicalSourceCLM_eq_lift (nativeL2ResidualCLM V (hF.toLp F)) hw.measurable (by
    filter_upwards [nativeL2ResidualCLM_agrees_continuous hκ0 hκ1 V hminus hplus F hF] with t ht
    rw [ht]
    exact hae' t)
  apply Lp.ext
  exact hleft.trans hright.symm

def nativeL2ParticularLaplacianCLM :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ∑ j : Fin 3,nativeL2ParticularSecondCLM hκ0 hκ1 V hminus hplus j j

theorem nativeL2ParticularLaplacianCLM_eq_source :
    nativeL2ParticularLaplacianCLM hκ0 hκ1 V hminus hplus=
      nativeL2HighPhysicalSourceCLM.comp (nativeL2ResidualCLM V) := by
  apply ContinuousLinearMap.ext
  intro F
  have hc := isClosed_eq (nativeL2ParticularLaplacianCLM hκ0 hκ1 V hminus hplus).continuous
    (nativeL2HighPhysicalSourceCLM.comp (nativeL2ResidualCLM V)).continuous
  refine (continuousL2SourceInclusion_dense (SpectralSpace AngularIndex)).induction_on F hc ?_
  intro H
  change nativeL2ParticularLaplacianCLM hκ0 hκ1 V hminus hplus (continuousL2SourceInclusion _ H)=_
  simp only [nativeL2ParticularLaplacianCLM,ContinuousLinearMap.sum_apply]
  simp_rw [(nativeL2ParticularCLM_agrees_continuous hκ0 hκ1 V hminus hplus H).2.2]
  exact nativeL2Particular_laplacian_continuous hκ0 hκ1 V hminus hplus H.val H.property

theorem nativeL2Particular_all_source_laplacian
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    (∑ j : Fin 3,nativeL2ParticularSecondCLM hκ0 hκ1 V hminus hplus j j F)=
      nativeL2HighPhysicalSourceCLM (nativeL2ResidualCLM V F) := by
  have he := DFunLike.congr_fun (nativeL2ParticularLaplacianCLM_eq_source hκ0 hκ1 V hminus hplus) F
  simpa only [nativeL2ParticularLaplacianCLM,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply] using he

#print axioms nativeL2Particular_laplacian_continuous
#print axioms nativeL2ParticularLaplacianCLM_eq_source
#print axioms nativeL2Particular_all_source_laplacian
end Yamabe3.Analysis.SpherePolar
