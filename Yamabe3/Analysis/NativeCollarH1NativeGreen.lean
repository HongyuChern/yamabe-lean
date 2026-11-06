import Yamabe3.Analysis.NativeCollarH1Gluing
import Yamabe3.Analysis.NativeCollarInteriorWeakGreen

/-! Native divergence equation for the one glued H1 function, with its
actual weak derivatives and the piecewise native volume source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

theorem nativeCollarGluedFunction_chosen_partial (J K : nativeCollarJetClosure)
    (hv : nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K) (j : Fin 3) :
    chosenWeakPartial' 2 j (nativeCollarGluedFunction J.val.1 K.val.1) nativePoissonEntranceCollar
      =ᵐ[volume.restrict nativePoissonEntranceCollar]
        nativeCollarGluedFunction (J.val.2.1 j) (K.val.2.1 j) := by
  have hu := nativeCollarGluedFunction_memH1 J K hv
  exact (chosenWeakPartial'_isWeakPartial_of_mem hu j).ae_eq (nativePolarTimeWindow_open (1/2))
    (nativeCollarGluedFunction_weak_partial J K hv j)
    ((chosenWeakPartial'_memLp_of_mem hu j).locallyIntegrable (by norm_num))
    ((nativeCollarGluedFunction_memLp _ _).locallyIntegrable (by norm_num))

def nativeCollarGluedDensityLaplacian (g : RiemannianMetric 3 E) (J K : nativeCollarJetClosure) : E → ℝ :=
  nativeCollarGluedFunction (nativeCollarDensityLaplacianCLM g J.val) (nativeCollarDensityLaplacianCLM g K.val)

theorem nativeCollarGluedDensityLaplacian_memLp (g : RiemannianMetric 3 E) (J K : nativeCollarJetClosure) :
    MemLp (nativeCollarGluedDensityLaplacian g J K) 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeCollarGluedFunction_memLp _ _

theorem nativeCollarGluedFunction_native_weak_equation (g : RiemannianMetric 3 E)
    (hGauss : ∀x v : E,g.inner x x v=inner ℝ x v) (J K : nativeCollarJetClosure)
    (hv : nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K)
    (hn : nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K)
    (ψ : E → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆nativePoissonEntranceCollar) :
    (∫x in nativePoissonEntranceCollar,ψ x*nativeCollarGluedDensityLaplacian g J K x)+
      (∑j : Fin 3,∫x in nativePoissonEntranceCollar,nativeCollarGradientTest g ψ j x*
        chosenWeakPartial' 2 j (nativeCollarGluedFunction J.val.1 K.val.1) nativePoissonEntranceCollar x)=0 := by
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hi := nativeCollarWeakGreen_interior g hGauss ψ hψ2 hc hs J
  have ho := nativeCollarWeakGreen g hGauss ψ hψ2 hc hs K
  have hb : nativeCollarNativeNormalPairCLM g ψ hψ.continuous J=nativeCollarNativeNormalPairCLM g ψ hψ.continuous K := by
    unfold nativeCollarNativeNormalPairCLM
    simp only [ContinuousLinearMap.comp_apply,hn]
  have hz : nativeCollarGreenRegionCLM (ball 0 1) isOpen_ball.measurableSet g ψ hψ2 J.val+
      nativeCollarGreenVolumeCLM g ψ hψ2 K.val=0 := by rw [hi,ho,hb,add_neg_cancel]
  simp only [nativeCollarGreenRegionCLM,nativeCollarGreenVolumeCLM,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,nativeCollarVolumePair_eq_integral] at hz
  have he (j : Fin 3) : (∫x in nativePoissonEntranceCollar,nativeCollarGradientTest g ψ j x*
      chosenWeakPartial' 2 j (nativeCollarGluedFunction J.val.1 K.val.1) nativePoissonEntranceCollar x)=
      ∫x in nativePoissonEntranceCollar,nativeCollarGradientTest g ψ j x*
        nativeCollarGluedFunction (J.val.2.1 j) (K.val.2.1 j) x := by
    apply integral_congr_ae
    filter_upwards [nativeCollarGluedFunction_chosen_partial J K hv j] with x hx
    rw [hx]
  simp_rw [he,nativeCollar_glued_test_pair_integral _ (continuous_nativeCollarGradientTest g hψ2 _)]
  change (∫x in nativePoissonEntranceCollar,ψ x*nativeCollarGluedFunction _ _ x)+_=0
  rw [nativeCollar_glued_test_pair_integral ψ hψ.continuous]
  simp only [Fin.sum_univ_three] at hz ⊢
  change (∫x in nativePoissonEntranceCollar ∩ ball 0 1,ψ x*(nativeCollarDensityLaplacianCLM g J.val : E → ℝ) x)+
    (((∫x in nativePoissonEntranceCollar ∩ ball 0 1,nativeCollarGradientTest g ψ 0 x*(J.val.2.1 0 : E → ℝ) x)+
    (∫x in nativePoissonEntranceCollar ∩ ball 0 1,nativeCollarGradientTest g ψ 1 x*(J.val.2.1 1 : E → ℝ) x))+
    (∫x in nativePoissonEntranceCollar ∩ ball 0 1,nativeCollarGradientTest g ψ 2 x*(J.val.2.1 2 : E → ℝ) x))+
    ((∫x in nativePoissonEntranceCollar ∩ {x : E | 1<‖x‖},ψ x*(nativeCollarDensityLaplacianCLM g K.val : E → ℝ) x)+
    (((∫x in nativePoissonEntranceCollar ∩ {x : E | 1<‖x‖},nativeCollarGradientTest g ψ 0 x*(K.val.2.1 0 : E → ℝ) x)+
    (∫x in nativePoissonEntranceCollar ∩ {x : E | 1<‖x‖},nativeCollarGradientTest g ψ 1 x*(K.val.2.1 1 : E → ℝ) x))+
    (∫x in nativePoissonEntranceCollar ∩ {x : E | 1<‖x‖},nativeCollarGradientTest g ψ 2 x*(K.val.2.1 2 : E → ℝ) x)))=0 at hz
  linarith only [hz]

#print axioms nativeCollarGluedFunction_chosen_partial
#print axioms nativeCollarGluedDensityLaplacian_memLp
#print axioms nativeCollarGluedFunction_native_weak_equation
end Yamabe3.Analysis.SpherePolar
