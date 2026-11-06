import Yamabe3.Analysis.NativeCollarJetWeakDerivatives
import Yamabe3.Analysis.NativeH4CollarRealization
import Yamabe3.Analysis.WeakCutoffCommutatorBound

/-! The literal flat cutoff commutator is a continuous linear operator
on the actual same-field collar jet. Its weak derivatives are identified
with those of the same annular field by uniqueness and restriction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.BoundaryLocalization Poincare.Analysis.Elliptic.Iteration

private theorem cutoff_partial_smooth {χ:E→ℝ} (hχ:ContDiff ℝ ∞ χ) (j:Fin 3) :
    ContDiff ℝ ∞ (partialDeriv j χ) :=
  (hχ.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const

def nativeCollarCutoffCommutatorCLM (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) :
    NativeCollarJet →L[ℝ] NativeCollarL2 :=
  nativeCollarJetPerturbationCLM (fun _ _ _=>0) (fun j x=> -2*partialDeriv j χ x)
    (fun x=> -(∑j:Fin 3,partialDeriv j (partialDeriv j χ) x))
    (fun _ _=>continuous_const)
    (fun j=>continuous_const.mul (cutoff_partial_smooth hχ j).continuous)
    ((continuous_finsetSum _ (fun j _=>
      (cutoff_partial_smooth (cutoff_partial_smooth hχ j) j).continuous)).neg)

theorem nativeCollarCutoffCommutator_ae (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (J:nativeCollarJetClosure) :
    (nativeCollarCutoffCommutatorCLM χ hχ J.val:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      weakCutoffCommutator nativePoissonEntranceCollar χ J.val.1 := by
  have hrow:=nativeCollarJetPerturbationCLM_ae (fun _ _ _=>0) (fun j x=> -2*partialDeriv j χ x)
    (fun x=> -(∑j:Fin 3,partialDeriv j (partialDeriv j χ) x))
    (fun _ _=>continuous_const)
    (fun j=>continuous_const.mul (cutoff_partial_smooth hχ j).continuous)
    ((continuous_finsetSum _ (fun j _=>
      (cutoff_partial_smooth (cutoff_partial_smooth hχ j) j).continuous)).neg) J.val
  have hj:=(nativeCollarJetClosure_chosen_jets J).1
  filter_upwards [hrow,eventually_all.mpr hj] with x hr hp
  dsimp only [nativeCollarCutoffCommutatorCLM]
  rw [hr]
  simp only [weakCutoffCommutator,hp,zero_mul,Finset.sum_const_zero,zero_add,Fin.sum_univ_three]
  ring

theorem nativeCollarCutoffCommutator_same_annular_field
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (J:nativeCollarJetClosure) {u:E→ℝ}
    (hu:MemWkp 1 2 u halfEndBasicAnnulus)
    (hv:(J.val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]u) :
    (nativeCollarCutoffCommutatorCLM χ hχ J.val:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      weakCutoffCommutator halfEndBasicAnnulus χ u := by
  have hO:=nativePolarTimeWindow_open (1/2)
  have hsub:=subset_closure.trans nativeEntranceCollar_closure_subset_basic
  have hp (j:Fin 3):chosenWeakPartial' 2 j J.val.1 nativePoissonEntranceCollar=ᵐ[volume.restrict nativePoissonEntranceCollar]
      chosenWeakPartial' 2 j u halfEndBasicAnnulus :=
    (chosenWeakPartial'_ae_congr (by norm_num) hO hv j).trans
      (chosenWeakPartial'_mono_set_ae (by norm_num) hO hsub hu.memW1p j).symm
  filter_upwards [nativeCollarCutoffCommutator_ae χ hχ J,hv,eventually_all.mpr hp] with x hc hx hp'
  rw [hc]
  simp only [weakCutoffCommutator,hx,hp']

#print axioms nativeCollarCutoffCommutatorCLM
#print axioms nativeCollarCutoffCommutator_ae
#print axioms nativeCollarCutoffCommutator_same_annular_field
end Yamabe3.Analysis.SpherePolar
