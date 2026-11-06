import Yamabe3.Analysis.BoundarySobolevMultiplier
import Yamabe3.Analysis.WeakLaplacianSobolev

/-! The actual finite first-order cutoff commutator has an L2 bound
from the same input's H1 norm. All cutoff/domain constants precede u. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryLocalization
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
open Poincare.Analysis.Elliptic.Iteration
local notation "E" => EuclideanSpace ℝ (Fin 3)

def weakCutoffCommutator (O:Set E) (χ u:E→ℝ):E→ℝ:=fun x=>
  -(∑i:Fin 3,(partialDeriv i (partialDeriv i χ) x*u x+
    2*partialDeriv i χ x*chosenWeakPartial' 2 i u O x))

theorem exists_weakCutoffCommutator_L2_bound {O:Set E} (hO:IsOpen O)
    (hOc:IsCompact (closure O)) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀u:E→ℝ,MemWkp 1 2 u O→
      MemLp (weakCutoffCommutator O χ u) 2 (volume.restrict O) ∧
      eLpNorm (weakCutoffCommutator O χ u) 2 (volume.restrict O)≤C*iteratedWeakSobolevNorm 1 2 u O := by
  have hχi(i:Fin 3):ContDiff ℝ ∞ (partialDeriv i χ):=
    (hχ.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hχii(i:Fin 3):ContDiff ℝ ∞ (partialDeriv i (partialDeriv i χ)):=
    ((hχi i).fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  choose A hA ha using fun i:Fin 3=>exists_compact_sobolev_multiplier_bound 0 hO hOc _ (hχii i)
  choose B hB hb using fun i:Fin 3=>exists_compact_sobolev_multiplier_bound 0 hO hOc
    (fun x=>2*partialDeriv i χ x) ((contDiff_const (c:=(2:ℝ))).mul (hχi i))
  refine ⟨∑i:Fin 3,(A i+B i),ENNReal.sum_ne_top.mpr (fun i _=>ENNReal.add_ne_top.mpr ⟨hA i,hB i⟩),fun u hu=>?_⟩
  let p:=fun i:Fin 3=>chosenWeakPartial' 2 i u O
  let R:=fun i:Fin 3=>fun x=>partialDeriv i (partialDeriv i χ) x*u x+(2*partialDeriv i χ x)*p i x
  have hR(i:Fin 3):MemWkp 0 2 (R i) O:=
    MemWkp.add (by norm_num) hO
      (memWkp_mul_smooth_of_isCompact_closure 0 hO hOc hu.memLp (hχii i))
      (memWkp_mul_smooth_of_isCompact_closure 0 hO hOc
        (chosenWeakPartial'_memLp_of_mem hu.memW1p i) ((contDiff_const (c:=(2:ℝ))).mul (hχi i)))
  have hr(i:Fin 3):iteratedWeakSobolevNorm 0 2 (R i) O≤(A i+B i)*iteratedWeakSobolevNorm 1 2 u O:=by
    have hh:=wkpNorm_add_le (by norm_num) hO
      (memWkp_mul_smooth_of_isCompact_closure 0 hO hOc hu.memLp (hχii i))
      (memWkp_mul_smooth_of_isCompact_closure 0 hO hOc
        (chosenWeakPartial'_memLp_of_mem hu.memW1p i) ((contDiff_const (c:=(2:ℝ))).mul (hχi i)))
    apply hh.trans
    apply (add_le_add (ha i u hu.memLp) (hb i (p i) (chosenWeakPartial'_memLp_of_mem hu.memW1p i))).trans
    calc
      _ ≤ A i*iteratedWeakSobolevNorm 1 2 u O+B i*iteratedWeakSobolevNorm 1 2 u O :=
        add_le_add (mul_le_mul le_rfl (wkpNorm_mono_order (by omega:0≤1) u O) zero_le zero_le)
          (mul_le_mul le_rfl (wkpNorm_chosenWeakPartial_le_wkpNorm_succ 0 2 u O i) zero_le zero_le)
      _ = _ := (add_mul _ _ _).symm
  have hs:=finite_sobolev_sum_with_bound hO 0 Finset.univ R (fun i _=>hR i)
  have he:weakCutoffCommutator O χ u=fun x=>-(∑i:Fin 3,R i x):=rfl
  rw [he]
  refine ⟨hs.1.memLp.neg,?_⟩
  change eLpNorm (-(fun x=>∑i:Fin 3,R i x)) 2 (volume.restrict O)≤_
  rw [eLpNorm_neg,←wkpNorm_zero]
  exact hs.2.trans ((Finset.sum_le_sum (fun i _=>hr i)).trans_eq (Finset.sum_mul _ _ _).symm)

#print axioms exists_weakCutoffCommutator_L2_bound
end Yamabe3.Analysis.UniformElliptic
