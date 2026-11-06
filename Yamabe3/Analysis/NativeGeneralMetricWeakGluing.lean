import Yamabe3.Analysis.WeakEquationPrecompactLocality
import Yamabe3.Analysis.NativeCollarGluedDivergence

/-! Equal actual value and radial traces already give one H2 field across
this coordinate sphere. Its true divergence equation therefore glues for
any smooth native metric; no radial Gauss normalization is imposed. -/
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

theorem nativeCollarDensityLaplacian_eq_negative_weakDivergence
    (g : RiemannianMetric 3 E) (J : nativeCollarJetClosure) :
    (nativeCollarDensityLaplacianCLM g J.val : E→ℝ)=ᵐ[volume.restrict D]
      (fun x => -weakDivergenceSource D (nativeDivergenceMatrix g) J.val.1 x) := by
  filter_upwards [nativeCollarDensityLaplacian_weak_ae g J] with x hx
  rw [hx]
  simp only [weakSecondOrderPerturbation,weakDivergenceSource,nativeCollarDivergenceFirst,
    zero_mul,add_zero,neg_neg,Finset.sum_add_distrib,Finset.sum_mul]
  congr 1
  exact Finset.sum_comm

theorem nativeCollarGluedFunction_general_divergence_equation
    (g : RiemannianMetric 3 E) (J K : nativeCollarJetClosure)
    (hv : nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K)
    (hn : nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K) :
    WeakEquation D
      (matrixFlux (nativeDivergenceMatrix g)
        (fun j => chosenWeakPartial' 2 j (nativeCollarGluedFunction J.val.1 K.val.1) D))
      (fun x => -nativeCollarGluedDensityLaplacian g J K x) := by
  classical
  let u := nativeCollarGluedFunction J.val.1 K.val.1
  have hD : IsOpen D := nativePolarTimeWindow_open (1/2)
  have hu1 := nativeCollarGluedFunction_memH1 J K hv
  have hu2 := nativeCollarGluedFunction_local_H2 J K hv hn
  apply weakEquation_of_precompact_local hD
  intro W hW hWc hWD
  have hsub : W⊆D := subset_closure.trans hWD
  have huW : MemWkp 2 2 u W := memWkp_on_precompact_of_locally hu2 hW hWc hWD
  have hp (j : Fin 3) := chosenWeakPartial'_mono_set_ae (by norm_num : (1:ℝ≥0∞) ≤ 2) hW hsub hu1 j
  have he := weakDivergenceSource_sphere_piecewise_ae hW hsub (nativeDivergenceMatrix g)
    huW (nativeCollarJetClosure_memH2 J) (nativeCollarJetClosure_memH2 K) (EventuallyEq.refl _ _)
  have hsrc : weakDivergenceSource W (nativeDivergenceMatrix g) u=ᵐ[volume.restrict W]
      (fun x => -nativeCollarGluedDensityLaplacian g J K x) := by
    filter_upwards [he,
      ae_restrict_of_ae_restrict_of_subset hsub (nativeCollarDensityLaplacian_eq_negative_weakDivergence g J),
      ae_restrict_of_ae_restrict_of_subset hsub (nativeCollarDensityLaplacian_eq_negative_weakDivergence g K)] with x hx hj hk
    rw [hx]
    by_cases hxB : x∈ball (0:E) 1
    · simp only [physicalSplitSource,nativeCollarGluedDensityLaplacian,nativeCollarGluedFunction,
        piecewise_eq_of_mem _ _ _ hxB,hj,neg_neg]
    · simp only [physicalSplitSource,nativeCollarGluedDensityLaplacian,nativeCollarGluedFunction,
        piecewise_eq_of_notMem _ _ _ hxB,hk,neg_neg]
  have hw := weakEquation_weakDivergenceSource hW (nativeDivergenceMatrix g)
    (contDiff_nativeDivergenceMatrix g) huW
  intro φ hφ hc hs
  calc
    _ = ∫x in W,∑i : Fin 3,matrixFlux (nativeDivergenceMatrix g)
        (fun j => chosenWeakPartial' 2 j u W) i x*partialDeriv i φ x := by
      apply integral_congr_ae
      filter_upwards [eventually_all.mpr hp] with x hx
      simp only [u,matrixFlux,hx]
    _ = ∫x in W,weakDivergenceSource W (nativeDivergenceMatrix g) u x*φ x := hw φ hφ hc hs
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hsrc] with x hx
      rw [hx]

#print axioms nativeCollarDensityLaplacian_eq_negative_weakDivergence
#print axioms nativeCollarGluedFunction_general_divergence_equation
end Yamabe3.Analysis.SpherePolar
