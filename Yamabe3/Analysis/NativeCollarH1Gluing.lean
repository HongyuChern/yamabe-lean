import Yamabe3.Analysis.NativeCollarFirstGreenSplit

/-! A single actual weak H1 function across the unit sphere. Equal value
traces remove the distributional jump; no volume representative is
restricted pointwise to the sphere. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

def nativeCollarGluedFunction (F G : NativeCollarL2) : E → ℝ := by
  classical
  exact (ball (0:E) 1).piecewise (F : E → ℝ) (G : E → ℝ)

theorem nativeCollarGluedFunction_memLp (F G : NativeCollarL2) :
    MemLp (nativeCollarGluedFunction F G) 2 (volume.restrict nativePoissonEntranceCollar) := by
  classical
  exact MemLp.piecewise isOpen_ball.measurableSet ((Lp.memLp F).mono_measure Measure.restrict_le_self)
    ((Lp.memLp G).mono_measure Measure.restrict_le_self)

theorem nativeCollar_glued_test_pair_integral (φ : E → ℝ) (hφ : Continuous φ) (F G : NativeCollarL2) :
    (∫x in nativePoissonEntranceCollar,φ x*nativeCollarGluedFunction F G x)=
      (∫x in nativePoissonEntranceCollar ∩ ball 0 1,φ x*(F : E → ℝ) x)+
      (∫x in nativePoissonEntranceCollar ∩ {y : E | 1<‖y‖},φ x*(G : E → ℝ) x) := by
  classical
  have he : (fun x => φ x*nativeCollarGluedFunction F G x)=
      (ball (0:E) 1).piecewise (fun x => φ x*(F : E → ℝ) x) (fun x => φ x*(G : E → ℝ) x) := by
    funext x
    by_cases hx : x∈ball (0:E) 1 <;> simp [nativeCollarGluedFunction,hx]
  rw [he,integral_piecewise isOpen_ball.measurableSet
    (nativeCollar_test_integrable φ hφ F).integrableOn (nativeCollar_test_integrable φ hφ G).integrableOn,
    setIntegral_congr_set (f := fun x => φ x*(G : E → ℝ) x) nativeCollar_ball_compl_ae]
  simp only [Measure.restrict_restrict isOpen_ball.measurableSet,
    Measure.restrict_restrict (isOpen_lt continuous_const continuous_norm).measurableSet,inter_comm]

theorem nativeCollarGluedFunction_weak_partial (J K : nativeCollarJetClosure)
    (hv : nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K) (j : Fin 3) :
    HasWeakPartialDeriv j (nativeCollarGluedFunction (J.val.2.1 j) (K.val.2.1 j))
      (nativeCollarGluedFunction J.val.1 K.val.1) nativePoissonEntranceCollar := by
  intro ψ hψ hc hs
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hi := nativeCollarWeakFirstGreen_interior ψ hψ hc hs j J
  have ho := nativeCollarWeakFirstGreen_exterior ψ hψ2 hc hs j K
  have hb : nativeCollarValueNormalPairCLM ψ hψ.continuous j J=
      nativeCollarValueNormalPairCLM ψ hψ.continuous j K := by
    unfold nativeCollarValueNormalPairCLM
    simp only [ContinuousLinearMap.comp_apply,hv]
  have hz : nativeCollarFirstGreenRegionCLM (ball 0 1) isOpen_ball.measurableSet ψ hψ2 j J.val+
      nativeCollarFirstGreenRegionCLM {x : E | 1<‖x‖} (isOpen_lt continuous_const continuous_norm).measurableSet ψ hψ2 j K.val=0 := by
    rw [hi,ho,hb,add_neg_cancel]
  have hiI := nativeCollar_test_integrable (partialDeriv j ψ) (native_partial_test_continuous hψ2 j)
  have hiD := nativeCollar_test_integrable ψ hψ.continuous
  rw [nativeCollarFirstGreenRegion_eq_integral,nativeCollarFirstGreenRegion_eq_integral,
    integral_add ((hiI J.val.1).mono_measure (Measure.restrict_mono inter_subset_left le_rfl))
      ((hiD (J.val.2.1 j)).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)),
    integral_add ((hiI K.val.1).mono_measure (Measure.restrict_mono inter_subset_left le_rfl))
      ((hiD (K.val.2.1 j)).mono_measure (Measure.restrict_mono inter_subset_left le_rfl))] at hz
  have he : (∫x in nativePoissonEntranceCollar,partialDeriv j ψ x*nativeCollarGluedFunction J.val.1 K.val.1 x)=
      -(∫x in nativePoissonEntranceCollar,ψ x*nativeCollarGluedFunction (J.val.2.1 j) (K.val.2.1 j) x) := by
    rw [nativeCollar_glued_test_pair_integral _ (native_partial_test_continuous hψ2 j),
      nativeCollar_glued_test_pair_integral _ hψ.continuous]
    linarith only [hz]
  simpa only [partialDeriv,mul_comm] using he

theorem nativeCollarGluedFunction_memH1 (J K : nativeCollarJetClosure)
    (hv : nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K) :
    MemW1p 2 (nativeCollarGluedFunction J.val.1 K.val.1) nativePoissonEntranceCollar :=
  ⟨nativeCollarGluedFunction_memLp _ _,fun j => ⟨nativeCollarGluedFunction (J.val.2.1 j) (K.val.2.1 j),
    nativeCollarGluedFunction_memLp _ _,nativeCollarGluedFunction_weak_partial J K hv j⟩⟩

#print axioms nativeCollarGluedFunction_memLp
#print axioms nativeCollar_glued_test_pair_integral
#print axioms nativeCollarGluedFunction_weak_partial
#print axioms nativeCollarGluedFunction_memH1
end Yamabe3.Analysis.SpherePolar
