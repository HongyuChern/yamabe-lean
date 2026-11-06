import Yamabe3.Analysis.NativeShellSourceReturn
import Yamabe3.Analysis.NativeL2FullSource

/-! The weighted-adjoint source return uses all angular modes. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeFullShellSourceReturnCLM (s : ℝ) : NativeCollarL2 →L[ℝ]
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) :=
  (ContinuousLinearMap.adjoint
    (nativeL2FullPhysicalSourceCLM.comp (l2TimeTranslateCLM (SpectralSpace AngularIndex) s))).comp
      nativeShellSourceWeightCLM

theorem nativeFullShellSourceReturn_norm (s : ℝ) :
    ‖nativeFullShellSourceReturnCLM s‖ ≤ ‖nativeL2FullPhysicalSourceCLM‖*Real.exp 1 := by
  have ht : ‖l2TimeTranslateCLM (SpectralSpace AngularIndex) s‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro F
    rw [l2TimeTranslate_norm,one_mul]
  have hl : ‖nativeL2FullPhysicalSourceCLM.comp
      (l2TimeTranslateCLM (SpectralSpace AngularIndex) s)‖ ≤ ‖nativeL2FullPhysicalSourceCLM‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (mul_one _))
  unfold nativeFullShellSourceReturnCLM
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  rw [LinearIsometryEquiv.norm_map]
  exact mul_le_mul hl nativeShellSourceWeightCLM_norm (norm_nonneg _) (norm_nonneg _)

theorem nativeFullShellSourceReturn_pairing (s : ℝ) (U : NativeCollarL2)
    (G : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    inner ℝ (nativeFullShellSourceReturnCLM s U) G =
      ∫ x in nativePoissonEntranceCollar,nativeShellSourceWeight x*U x*
        (nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM (SpectralSpace AngularIndex) s G) : E → ℝ) x := by
  simp only [nativeFullShellSourceReturnCLM,ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_left,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [nativeShellSourceWeightCLM_ae U] with x hx
  simp only [RCLike.inner_apply,conj_trivial,hx,ContinuousLinearMap.comp_apply]
  ring

#print axioms nativeFullShellSourceReturn_norm
#print axioms nativeFullShellSourceReturn_pairing
end Yamabe3.Analysis.SpherePolar
