import Yamabe3.Analysis.NativeGeneralMetricWeakGluing

/-! Actual native Green volume pairings cancel for the already matched
jets under every smooth metric. No Gauss condition or radial-flux
identification is inserted. These are physical density/gradient pairings;
identification with a particular pointwise unit normal is separate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates
local notation "D" => nativePoissonEntranceCollar

theorem nativeCollarGluedFunction_general_native_weak_equation
    (g : RiemannianMetric 3 E) (J K : nativeCollarJetClosure)
    (hv : nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K)
    (hn : nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K)
    (ψ : E→ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆D) :
    (∫x in D,ψ x*nativeCollarGluedDensityLaplacian g J K x)+
      (∑j : Fin 3,∫x in D,nativeCollarGradientTest g ψ j x*
        chosenWeakPartial' 2 j (nativeCollarGluedFunction J.val.1 K.val.1) D x)=0 := by
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hu := nativeCollarGluedFunction_memH1 J K hv
  have hi (j : Fin 3) : Integrable (fun x => nativeCollarGradientTest g ψ j x*
      chosenWeakPartial' 2 j (nativeCollarGluedFunction J.val.1 K.val.1) D x) (volume.restrict D) := by
    have ht := native_memLp_two_of_continuousOn_precompact
      (nativePolarTimeWindow_open (1/2)).measurableSet (nativePolarTimeWindow_precompact (1/2))
      (nativePolarTimeWindow_closure_offZero (1/2))
      (continuous_nativeCollarGradientTest g hψ2 j).continuousOn
    exact ht.integrable_mul (chosenWeakPartial'_memLp_of_mem hu j)
  have hz := nativeCollarGluedFunction_general_divergence_equation g J K hv hn ψ hψ hc hs
  have he (x : E) : (∑i : Fin 3,matrixFlux (nativeDivergenceMatrix g)
      (fun j => chosenWeakPartial' 2 j (nativeCollarGluedFunction J.val.1 K.val.1) D) i x*partialDeriv i ψ x)=
      ∑j : Fin 3,nativeCollarGradientTest g ψ j x*
        chosenWeakPartial' 2 j (nativeCollarGluedFunction J.val.1 K.val.1) D x := by
    simp only [matrixFlux,nativeCollarGradientTest,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he] at hz
  rw [integral_finsetSum _ (fun j _ => hi j)] at hz
  have hr : (∫x in D, -nativeCollarGluedDensityLaplacian g J K x*ψ x)=
      -(∫x in D,ψ x*nativeCollarGluedDensityLaplacian g J K x) := by
    rw [←integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by ring)
  rw [hr] at hz
  linarith only [hz]

theorem nativeCollar_general_metric_Green_matching
    (g : RiemannianMetric 3 E) (J K : nativeCollarJetClosure)
    (hv : nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K)
    (hn : nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K)
    (ψ : E→ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆D) :
    let hψ2 := hψ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    8*nativeCollarGreenRegionCLM (ball (0:E) 1) isOpen_ball.measurableSet g ψ hψ2 J.val+
      8*nativeCollarGreenVolumeCLM g ψ hψ2 K.val=0 := by
  dsimp only
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hz := nativeCollarGluedFunction_general_native_weak_equation g J K hv hn ψ hψ hc hs
  have he (j : Fin 3) : (∫x in D,nativeCollarGradientTest g ψ j x*
      chosenWeakPartial' 2 j (nativeCollarGluedFunction J.val.1 K.val.1) D x)=
      ∫x in D,nativeCollarGradientTest g ψ j x*
        nativeCollarGluedFunction (J.val.2.1 j) (K.val.2.1 j) x := by
    apply integral_congr_ae
    filter_upwards [nativeCollarGluedFunction_chosen_partial J K hv j] with x hx
    rw [hx]
  simp_rw [he,nativeCollar_glued_test_pair_integral _ (continuous_nativeCollarGradientTest g hψ2 _)] at hz
  change (∫x in D,ψ x*nativeCollarGluedFunction _ _ x)+_=0 at hz
  rw [nativeCollar_glued_test_pair_integral ψ hψ.continuous] at hz
  simp only [nativeCollarGreenRegionCLM,nativeCollarGreenVolumeCLM,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,nativeCollarVolumePair_eq_integral]
  have hproj (j : Fin 3) (Q : NativeCollarJet) : nativeCollarJetFirstCLM j Q=Q.2.1 j := rfl
  simp only [hproj,Fin.sum_univ_three] at hz ⊢
  linarith only [hz]

#print axioms nativeCollarGluedFunction_general_native_weak_equation
#print axioms nativeCollar_general_metric_Green_matching
end Yamabe3.Analysis.SpherePolar
