import Yamabe3.Analysis.NativeOuterWindowReconstruction
import Yamabe3.Analysis.NativeSupportedOuterAllScaleEquation
import Yamabe3.Analysis.NativeFullShellEquation

/-! Negative shell returns use only the TRUE exterior equation.
The interface endpoint has zero ambient volume; no volume-a.e. equality
is restricted to a surface and no equation of the artificial extension
is invoked. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic

theorem nativeSourceShell_ae_negativeScale (n:ℕ) :
    ∀ᵐx:E∂volume.restrict nativeSourceShell,x∈nativeNegativeScaledCollar (nativeOuterLogShellCenter n) := by
  let s:=nativeOuterLogShellCenter n
  have hnot:∀ᵐx:E∂volume,x∉sphere (0:E) (Real.exp s) := by
    simp only [ae_iff,not_not,setOf_mem_eq]
    exact Measure.addHaar_sphere volume (0:E) (Real.exp s)
  filter_upwards [ae_restrict_of_ae hnot,ae_restrict_mem nativeSourceShell_measurable] with x hn hx
  refine ⟨nativeSourceShell_subset_collar hx,?_⟩
  have hxn:0 < ‖x‖ := norm_pos_iff.mpr hx.1
  have hs:s ≤ Real.log ‖x‖ := by
    have hn0:(0:ℝ) ≤ n := Nat.cast_nonneg n
    dsimp only [s,nativeOuterLogShellCenter]
    linarith [hx.2.2]
  have hle:Real.exp s ≤ ‖x‖ := (Real.exp_le_exp.mpr hs).trans_eq (Real.exp_log hxn)
  exact lt_of_le_of_ne hle (by
    intro he
    exact hn (by rw [mem_sphere,dist_zero_right];exact he.symm))

theorem nativeFullShellSourceReturn_eq_of_negativeRestriction (n:ℕ) (U W:NativeCollarL2)
    (he:nativeNegativeScaledRestrictionCLM (nativeOuterLogShellCenter n) U=
      nativeNegativeScaledRestrictionCLM (nativeOuterLogShellCenter n) W) :
    nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter n) U=
      nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter n) W := by
  let D:=nativeNegativeScaledCollar (nativeOuterLogShellCenter n)
  have hD:MeasurableSet D := (nativeNegativeScaledCollar_open _).measurableSet
  have hμ:volume.restrict D ≤ volume.restrict nativePoissonEntranceCollar :=
    Measure.restrict_mono inter_subset_left le_rfl
  have hU:(nativeNegativeScaledRestrictionCLM (nativeOuterLogShellCenter n) U:E→ℝ)=ᵐ[volume.restrict D] (U:E→ℝ) :=
    l2MeasureRestrict_ae hμ U
  have hW:(nativeNegativeScaledRestrictionCLM (nativeOuterLogShellCenter n) W:E→ℝ)=ᵐ[volume.restrict D] (W:E→ℝ) :=
    l2MeasureRestrict_ae hμ W
  rw [he] at hU
  have hglobal:∀ᵐx:E∂volume,x∈D → U x=W x := (ae_restrict_iff' hD).mp (hU.symm.trans hW)
  apply nativeFullShellSourceReturn_eq_of_shell_ae
  filter_upwards [ae_restrict_of_ae hglobal,nativeSourceShell_ae_negativeScale n] with x hx hD
  exact hx hD

#print axioms nativeSourceShell_ae_negativeScale
#print axioms nativeFullShellSourceReturn_eq_of_negativeRestriction
end Yamabe3.Analysis.SpherePolar
