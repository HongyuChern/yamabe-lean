import Yamabe3.Analysis.NativeHighSourceReconstruction
import Yamabe3.Analysis.NativeL2HalfAllScaleEquation

/-! Shell returns only use the positive-time region on which the true
half-end equation is proved; reflected negative-time values never supply
an equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeSourceShell_subset_positiveScale (n : ℕ) :
    nativeSourceShell ⊆ nativePositiveScaledCollar (nativeLogShellCenter n) := by
  intro x hx
  refine ⟨nativeSourceShell_subset_collar hx,?_⟩
  have ht := hx.2.1
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  have hnrm : 0<‖x‖ := norm_pos_iff.mpr hx.1
  rw [Metric.mem_ball,dist_zero_right]
  calc
    ‖x‖ = Real.exp (Real.log ‖x‖) := (Real.exp_log hnrm).symm
    _ < Real.exp (nativeLogShellCenter n) := Real.exp_lt_exp.mpr (by
      unfold nativeLogShellCenter
      linarith)

theorem nativeShellSourceReturn_eq_of_shell_ae (s : ℝ) (U W : NativeCollarL2)
    (he : (U : E → ℝ)=ᵐ[volume.restrict nativeSourceShell] (W : E → ℝ)) :
    nativeShellSourceReturnCLM s U=nativeShellSourceReturnCLM s W := by
  have hm : nativeShellSourceWeightCLM U=nativeShellSourceWeightCLM W := by
    apply Lp.ext
    have he' := ae_restrict_of_ae (s := nativePoissonEntranceCollar)
      ((ae_restrict_iff' nativeSourceShell_measurable).mp he)
    filter_upwards [nativeShellSourceWeightCLM_ae U,nativeShellSourceWeightCLM_ae W,he'] with x hu hw he
    rw [hu,hw]
    by_cases hx : x∈nativeSourceShell
    · rw [he hx]
    · simp only [nativeShellSourceWeight,indicator_of_notMem hx,zero_mul]
  simp only [nativeShellSourceReturnCLM,ContinuousLinearMap.comp_apply,hm]

theorem nativeShellSourceReturn_eq_of_positiveRestriction (n : ℕ) (U W : NativeCollarL2)
    (he : nativePositiveScaledRestrictionCLM (nativeLogShellCenter n) U=
      nativePositiveScaledRestrictionCLM (nativeLogShellCenter n) W) :
    nativeShellSourceReturnCLM (nativeLogShellCenter n) U=
      nativeShellSourceReturnCLM (nativeLogShellCenter n) W := by
  let D := nativePositiveScaledCollar (nativeLogShellCenter n)
  have hμ : volume.restrict D≤volume.restrict nativePoissonEntranceCollar :=
    Measure.restrict_mono inter_subset_left le_rfl
  have hU : (nativePositiveScaledRestrictionCLM (nativeLogShellCenter n) U : E → ℝ)=ᵐ[volume.restrict D] (U : E → ℝ) :=
    l2MeasureRestrict_ae hμ U
  have hW : (nativePositiveScaledRestrictionCLM (nativeLogShellCenter n) W : E → ℝ)=ᵐ[volume.restrict D] (W : E → ℝ) :=
    l2MeasureRestrict_ae hμ W
  rw [he] at hU
  apply nativeShellSourceReturn_eq_of_shell_ae
  exact ae_mono (Measure.restrict_mono (nativeSourceShell_subset_positiveScale n) le_rfl) (hU.symm.trans hW)

theorem nativeHalfEquation_shell_return (P : NativeHighPotential)
    (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
    (n : ℕ) (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeShellSourceReturnCLM (nativeLogShellCenter n)
      ((∑ j : Fin 3,nativeL2HalfAllScaleSecondCLM P hp (nativeLogShellCenter n) j j F)+
        nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ (nativeLogShellCenter n) P.potential)
          (nativeL2HalfAllScaleValueCLM P hp (nativeLogShellCenter n) F))=
    nativeShellSourceReturnCLM (nativeLogShellCenter n)
      (nativeL2HighPhysicalSourceCLM (l2TimeTranslateCLM (SpectralSpace AngularIndex) (nativeLogShellCenter n) F)) :=
  nativeShellSourceReturn_eq_of_positiveRestriction n _ _ (nativeL2HalfAllScale_physical_equation P hp _ F)

#print axioms nativeSourceShell_subset_positiveScale
#print axioms nativeShellSourceReturn_eq_of_shell_ae
#print axioms nativeShellSourceReturn_eq_of_positiveRestriction
#print axioms nativeHalfEquation_shell_return
end Yamabe3.Analysis.SpherePolar
