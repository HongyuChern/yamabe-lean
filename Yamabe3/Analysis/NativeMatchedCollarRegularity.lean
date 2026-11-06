import Yamabe3.Analysis.NativeMatchedWeakBoundaryAssembly
import Yamabe3.Analysis.NativeEuclideanSphereFirstGreen
import PoincareLib.Analysis.Elliptic.Regularity.Iteration.Bootstrap

/-! Equal actual value and normal traces produce the weak equation of the
literal glued function. The same function gains local H2 across the sphere;
this is not inferred just from regularity on the two separate sides. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

theorem nativeCollarGluedFunction_divergence_equation
    (g : RiemannianMetric 3 E) (hGauss : ∀x v : E,g.inner x x v=inner ℝ x v)
    (J K : nativeCollarJetClosure)
    (hv : nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K)
    (hn : nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K) :
    WeakEquation nativePoissonEntranceCollar
      (matrixFlux (nativeDivergenceMatrix g)
        (fun j => chosenWeakPartial' 2 j (nativeCollarGluedFunction J.val.1 K.val.1) nativePoissonEntranceCollar))
      (fun x => -nativeCollarGluedDensityLaplacian g J K x) := by
  intro ψ hψ hc hs
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hu := nativeCollarGluedFunction_memH1 J K hv
  have hi (j : Fin 3) : Integrable (fun x => nativeCollarGradientTest g ψ j x*
      chosenWeakPartial' 2 j (nativeCollarGluedFunction J.val.1 K.val.1) nativePoissonEntranceCollar x)
      (volume.restrict nativePoissonEntranceCollar) := by
    have ht := native_memLp_two_of_continuousOn_precompact
      (nativePolarTimeWindow_open (1/2)).measurableSet (nativePolarTimeWindow_precompact (1/2))
      (nativePolarTimeWindow_closure_offZero (1/2))
      (continuous_nativeCollarGradientTest g hψ2 j).continuousOn
    exact ht.integrable_mul (chosenWeakPartial'_memLp_of_mem hu j)
  have hz := nativeCollarGluedFunction_native_weak_equation g hGauss J K hv hn ψ hψ hc hs
  have he (x : E) : (∑i : Fin 3,matrixFlux (nativeDivergenceMatrix g)
      (fun j => chosenWeakPartial' 2 j (nativeCollarGluedFunction J.val.1 K.val.1) nativePoissonEntranceCollar) i x*partialDeriv i ψ x)=
      ∑j : Fin 3,nativeCollarGradientTest g ψ j x*
        chosenWeakPartial' 2 j (nativeCollarGluedFunction J.val.1 K.val.1) nativePoissonEntranceCollar x := by
    simp only [matrixFlux,nativeCollarGradientTest,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ => hi j)]
  have hr : (∫x in nativePoissonEntranceCollar, -nativeCollarGluedDensityLaplacian g J K x*ψ x)=
      -(∫x in nativePoissonEntranceCollar,ψ x*nativeCollarGluedDensityLaplacian g J K x) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by ring)
  rw [hr]
  linarith only [hz]

theorem nativeCollarGluedFunction_local_H2 (J K : nativeCollarJetClosure)
    (hv : nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K)
    (hn : nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K) :
    MemWkpLocally 2 (nativeCollarGluedFunction J.val.1 K.val.1) nativePoissonEntranceCollar := by
  have hu := nativeCollarGluedFunction_memH1 J K hv
  have he := nativeCollarGluedFunction_divergence_equation (RiemannianMetric.euclideanMetric 3)
    (fun x v => rfl) J K hv hn
  have hf : MemWkpLocally 0 (fun x => -nativeCollarGluedDensityLaplacian (RiemannianMetric.euclideanMetric 3) J K x)
      nativePoissonEntranceCollar :=
    locally_of_memWkp (nativePolarTimeWindow_open (1/2)) (nativeCollarGluedDensityLaplacian_memLp _ J K).neg
  apply memWkpLocally_add_two_of_weakEquation 0 (nativePolarTimeWindow_open (1/2))
    (A := fun _ : E => (1 : Matrix (Fin 3) (Fin 3) ℝ))
    (fun _ _ => contDiff_const) (fun _ _ => Matrix.PosDef.one) hu.1
    (fun j => chosenWeakPartial'_memLp_of_mem hu j)
    (fun j => chosenWeakPartial'_isWeakPartial_of_mem hu j) hf
  have hA : nativeDivergenceMatrix (RiemannianMetric.euclideanMetric 3) =
      (fun _ : E => (1 : Matrix (Fin 3) (Fin 3) ℝ)) :=
    funext nativeEuclidean_divergence_matrix
  rw [hA] at he
  exact he

#print axioms nativeCollarGluedFunction_divergence_equation
#print axioms nativeCollarGluedFunction_local_H2
end Yamabe3.Analysis.SpherePolar
