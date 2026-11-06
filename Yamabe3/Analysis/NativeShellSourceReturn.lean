import Yamabe3.Analysis.NativeCollarJetSpace
import Yamabe3.Analysis.NativeL2PhysicalSource
import Yamabe3.Analysis.NativeCollarPotentialMultiplier
import Yamabe3.Analysis.L2TimeTranslation
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! A real bounded source return from a physical collar. The weight is
|x|^-2 on a disjoint-shell window. Its defining adjoint pairing retains
Euclidean volume and the actual high angular lift; it is not an assumed
inverse of the source map. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeSourceShell : Set E := nativePolarTimeWindow (Ioc (-(1/4:ℝ)) (1/4))

theorem nativeSourceShell_measurable : MeasurableSet nativeSourceShell :=
  nativePolarTimeWindow_measurable measurableSet_Ioc

def nativeShellSourceWeight : E → ℝ := nativeSourceShell.indicator
  (nativeHalfEndPotentialCoefficient (BoundedContinuousFunction.const ℝ (1:ℝ)))

theorem nativeShellSourceWeight_measurable : Measurable nativeShellSourceWeight :=
  (nativeCollarPotential_measurable _).indicator nativeSourceShell_measurable

theorem nativeShellSourceWeight_bound {x : E} (hx : x∈nativePoissonEntranceCollar) :
    ‖nativeShellSourceWeight x‖ ≤ Real.exp 1 := by
  by_cases hs : x∈nativeSourceShell
  · simpa only [nativeShellSourceWeight,indicator_of_mem hs,
      BoundedContinuousFunction.norm_const_eq,norm_one,one_mul] using
      nativeCollarPotential_bound (BoundedContinuousFunction.const ℝ (1:ℝ)) hx
  · simp only [nativeShellSourceWeight,indicator_of_notMem hs,norm_zero]
    exact (Real.exp_pos 1).le

def nativeShellSourceWeightCLM : NativeCollarL2 →L[ℝ] NativeCollarL2 :=
  l2ScalarMulCLM nativeShellSourceWeight nativeShellSourceWeight_measurable.aestronglyMeasurable
    (Real.exp 1) (Real.exp_pos 1).le (by
      filter_upwards [ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hx
      exact nativeShellSourceWeight_bound hx)

theorem nativeShellSourceWeightCLM_ae (U : NativeCollarL2) :
    (nativeShellSourceWeightCLM U : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => nativeShellSourceWeight x*U x) :=
  l2ScalarMul_ae nativeShellSourceWeight nativeShellSourceWeight_measurable.aestronglyMeasurable
    (Real.exp 1) (Real.exp_pos 1).le (by
      filter_upwards [ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hx
      exact nativeShellSourceWeight_bound hx) U

theorem nativeShellSourceWeightCLM_norm : ‖nativeShellSourceWeightCLM‖ ≤ Real.exp 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos 1).le
  intro U
  exact l2ScalarMul_norm_le nativeShellSourceWeight nativeShellSourceWeight_measurable.aestronglyMeasurable
    (Real.exp 1) (Real.exp_pos 1).le (by
      filter_upwards [ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hx
      exact nativeShellSourceWeight_bound hx) U

def nativeShellSourceReturnCLM (s : ℝ) : NativeCollarL2 →L[ℝ]
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) :=
  (ContinuousLinearMap.adjoint
    (nativeL2HighPhysicalSourceCLM.comp (l2TimeTranslateCLM (SpectralSpace AngularIndex) s))).comp
      nativeShellSourceWeightCLM

theorem nativeShellSourceReturn_norm (s : ℝ) :
    ‖nativeShellSourceReturnCLM s‖ ≤ ‖nativeL2HighPhysicalSourceCLM‖*Real.exp 1 := by
  have ht : ‖l2TimeTranslateCLM (SpectralSpace AngularIndex) s‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro F
    rw [l2TimeTranslate_norm,one_mul]
  have hl : ‖nativeL2HighPhysicalSourceCLM.comp
      (l2TimeTranslateCLM (SpectralSpace AngularIndex) s)‖ ≤ ‖nativeL2HighPhysicalSourceCLM‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (mul_one _))
  unfold nativeShellSourceReturnCLM
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  rw [LinearIsometryEquiv.norm_map]
  exact mul_le_mul hl nativeShellSourceWeightCLM_norm (norm_nonneg _) (norm_nonneg _)

theorem nativeShellSourceReturn_pairing (s : ℝ) (U : NativeCollarL2)
    (G : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    inner ℝ (nativeShellSourceReturnCLM s U) G =
      ∫ x in nativePoissonEntranceCollar,nativeShellSourceWeight x*U x*
        (nativeL2HighPhysicalSourceCLM (l2TimeTranslateCLM (SpectralSpace AngularIndex) s G) : E → ℝ) x := by
  simp only [nativeShellSourceReturnCLM,ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_left,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [nativeShellSourceWeightCLM_ae U] with x hx
  simp only [RCLike.inner_apply,conj_trivial,hx,ContinuousLinearMap.comp_apply]
  ring

#print axioms nativeSourceShell_measurable
#print axioms nativeShellSourceWeightCLM_ae
#print axioms nativeShellSourceWeightCLM_norm
#print axioms nativeShellSourceReturn_norm
#print axioms nativeShellSourceReturn_pairing
end Yamabe3.Analysis.SpherePolar
