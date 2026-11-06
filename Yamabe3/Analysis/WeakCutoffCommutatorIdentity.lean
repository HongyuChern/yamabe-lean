import Yamabe3.Analysis.WeakCutoffCommutatorBound
import Yamabe3.Analysis.WeakDivergenceDirectional
import Yamabe3.Analysis.NativeCollarJetWeakDerivatives

/-! The commutator bound is attached to the actual weak Laplacian of
cutoff times the same H2 function; it is not an independently assigned source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryLocalization Poincare.Analysis.Elliptic.Iteration
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem weakNegativeLaplacian_cutoff_commutator {O:Set E} (hO:IsOpen O)
    (hOc:IsCompact (closure O)) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    {u:E→ℝ} (hu:MemWkp 2 2 u O) :
    (fun x=>weakNegativeLaplacian O (fun y=>χ y*u y) x-χ x*weakNegativeLaplacian O u x)
      =ᵐ[volume.restrict O]weakCutoffCommutator O χ u := by
  let p:=fun i:Fin 3=>chosenWeakPartial' 2 i u O
  let q:=fun i:Fin 3=>chosenWeakPartial' 2 i (p i) O
  let a:=fun i:Fin 3=>partialDeriv i χ
  let b:=fun i:Fin 3=>partialDeriv i (a i)
  have ha(i:Fin 3):ContDiff ℝ ∞ (a i):=(hχ.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hb(i:Fin 3):ContDiff ℝ ∞ (b i):=((ha i).fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hp(i:Fin 3):MemWkp 1 2 (p i) O:=hu.chosenWeakPartial_mem i
  have hq(i:Fin 3):MemLp (q i) 2 (volume.restrict O):=chosenWeakPartial'_memLp_of_mem (hp i).memW1p i
  have hχu:MemWkp 2 2 (fun x=>χ x*u x) O:=memWkp_mul_smooth_of_isCompact_closure 2 hO hOc hu hχ
  have hpp(i:Fin 3):chosenWeakPartial' 2 i (chosenWeakPartial' 2 i (fun y=>χ y*u y) O) O=ᵐ[volume.restrict O]
      (fun x=>(χ x*q i x+a i x*p i x)+(a i x*p i x+b i x*u x)):=by
    have hA:MemLp (fun x=>χ x*p i x) 2 (volume.restrict O):=
      (memWkp_mul_smooth_of_isCompact_closure 0 hO hOc (hp i).memLp hχ).memLp
    have hB:MemLp (fun x=>a i x*u x) 2 (volume.restrict O):=
      (memWkp_mul_smooth_of_isCompact_closure 0 hO hOc hu.memLp (ha i)).memLp
    have hDA:MemLp (fun x=>χ x*q i x+a i x*p i x) 2 (volume.restrict O):=
      ((memWkp_mul_smooth_of_isCompact_closure 0 hO hOc (hq i) hχ).memLp).add
        ((memWkp_mul_smooth_of_isCompact_closure 0 hO hOc (hp i).memLp (ha i)).memLp)
    have hDB:MemLp (fun x=>a i x*p i x+b i x*u x) 2 (volume.restrict O):=
      ((memWkp_mul_smooth_of_isCompact_closure 0 hO hOc (hp i).memLp (ha i)).memLp).add
        ((memWkp_mul_smooth_of_isCompact_closure 0 hO hOc hu.memLp (hb i)).memLp)
    have hwA:HasWeakPartialDeriv i (fun x=>χ x*q i x+a i x*p i x) (fun x=>χ x*p i x) O:=
      (chosenWeakPartial'_isWeakPartial_of_mem (hp i).memW1p i).mul_smooth hO hχ
        ((hp i).memLp.locallyIntegrable (by norm_num)) ((hq i).locallyIntegrable (by norm_num))
    have hwB:HasWeakPartialDeriv i (fun x=>a i x*p i x+b i x*u x) (fun x=>a i x*u x) O:=
      (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i).mul_smooth hO (ha i)
        (hu.memLp.locallyIntegrable (by norm_num)) ((hp i).memLp.locallyIntegrable (by norm_num))
    have hw:=weakPartial_add_memLp hA hB hDA hDB hwA hwB
    have he:=compact_product_chosen_partial_ae hO hOc hχ hu.memW1p i
    have hwt:=native_weakPartial_transfer_ae he (ae_eq_rfl) hw
    exact (chosenWeakPartial'_isWeakPartial_of_mem (hχu.chosenWeakPartial_mem i).memW1p i).ae_eq hO hwt
      ((chosenWeakPartial'_memLp_of_mem (hχu.chosenWeakPartial_mem i).memW1p i).locallyIntegrable (by norm_num))
      ((hDA.add hDB).locallyIntegrable (by norm_num))
  filter_upwards [eventually_all.mpr hpp] with x hx
  change -(∑i:Fin 3,chosenWeakPartial' 2 i (chosenWeakPartial' 2 i (fun y=>χ y*u y) O) O x)-
    χ x*(-(∑i:Fin 3,q i x))=-(∑i:Fin 3,(b i x*u x+2*a i x*p i x))
  simp only [hx,Fin.sum_univ_three]
  ring

#print axioms weakNegativeLaplacian_cutoff_commutator
end Yamabe3.Analysis.UniformElliptic
