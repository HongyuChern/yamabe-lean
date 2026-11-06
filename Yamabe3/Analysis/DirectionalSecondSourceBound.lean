import Yamabe3.Analysis.WeakDivergenceDirectional

/-! The next directional commutator has a constructed L2 witness and a
source-uniform bound. No global normal derivative of a jumping source is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_second_directional_source_bound {O : Set E} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (a : E → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j,ContDiff ℝ ∞ (fun x => a x i j)) (k s : Fin d) :
    ∃ C : ℝ≥0∞, C≠⊤ ∧ ∀ u r t : E → ℝ,
      MemWkp 2 2 u O → MemWkp 2 2 (chosenWeakPartial' 2 s u O) O →
      MemLp r 2 (volume.restrict O) → MemLp t 2 (volume.restrict O) → HasWeakPartialDeriv s t r O →
      ∃ T : E → ℝ, MemLp T 2 (volume.restrict O) ∧
        HasWeakPartialDeriv s T
          (differentiatedSource a (fun j => chosenWeakPartial' 2 j u O)
            (fun i j => chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u O) O) r k) O ∧
        iteratedWeakSobolevNorm 0 2 T O ≤ iteratedWeakSobolevNorm 0 2 t O+C *
          (iteratedWeakSobolevNorm 2 2 u O+
            iteratedWeakSobolevNorm 2 2 (chosenWeakPartial' 2 s u O) O) := by
  let da : E → Matrix (Fin d) (Fin d) ℝ := fun x i j => partialDeriv k (fun y => a y i j) x
  let dda : E → Matrix (Fin d) (Fin d) ℝ := fun x i j => partialDeriv s (fun y => da y i j) x
  have hda (i j : Fin d) : ContDiff ℝ ∞ (fun x => da x i j) := contDiff_partial (ha i j) k
  have hdda (i j : Fin d) : ContDiff ℝ ∞ (fun x => dda x i j) := contDiff_partial (hda i j) s
  obtain ⟨A,hA,hbA⟩ := exists_weakDivergenceSource_bound hO hOc da hda
  obtain ⟨B,hB,hbB⟩ := exists_weakDivergenceSource_bound hO hOc dda hdda
  refine ⟨A+B,by finiteness,?_⟩
  intro u r t hu hv hr ht hrt
  let v := chosenWeakPartial' 2 s u O
  let F := weakDivergenceSource O da u
  let G := fun x => weakDivergenceSource O da v x+weakDivergenceSource O dda u x
  let T := fun x => t x-G x
  have hF : MemLp F 2 (volume.restrict O) := (hbA u hu).1
  have hG : MemLp G 2 (volume.restrict O) := ((hbA v hv).1.memLp).add (hbB u hu).1.memLp
  have hT : MemLp T 2 (volume.restrict O) := ht.sub hG
  have hFG : HasWeakPartialDeriv s G F O := weakPartial_weakDivergenceSource hO hOc da hda hu s hv
  have hbase := weakPartial_add_memLp hr hF.neg ht hG.neg hrt (weakPartial_neg_exact hFG)
  have hsource := differentiatedSource_eq_weak_commutator_ae hO a k hu r
  refine ⟨T,hT,?_,?_⟩
  · apply hasWeakPartialDeriv_congr_ae hO s hsource.symm
    simpa only [T,F,da,Pi.neg_apply,sub_eq_add_neg] using hbase
  · calc
      _ ≤ iteratedWeakSobolevNorm 0 2 t O+iteratedWeakSobolevNorm 0 2 G O :=
        sobolevNorm_sub_le (k:=0) hO ht hG
      _ ≤ iteratedWeakSobolevNorm 0 2 t O+
          (iteratedWeakSobolevNorm 0 2 (weakDivergenceSource O da v) O+
            iteratedWeakSobolevNorm 0 2 (weakDivergenceSource O dda u) O) :=
        add_le_add le_rfl (wkpNorm_add_le (by norm_num) hO (hbA v hv).1 (hbB u hu).1)
      _ ≤ iteratedWeakSobolevNorm 0 2 t O+
          (A*iteratedWeakSobolevNorm 2 2 v O+B*iteratedWeakSobolevNorm 2 2 u O) :=
        add_le_add le_rfl (add_le_add (hbA v hv).2 (hbB u hu).2)
      _ ≤ _ := by
        apply add_le_add le_rfl
        calc
          _ ≤ A*(iteratedWeakSobolevNorm 2 2 u O+iteratedWeakSobolevNorm 2 2 v O)+
              B*(iteratedWeakSobolevNorm 2 2 u O+iteratedWeakSobolevNorm 2 2 v O) :=
            add_le_add (mul_le_mul le_rfl (le_add_left le_rfl) zero_le zero_le)
              (mul_le_mul le_rfl (le_add_right le_rfl) zero_le zero_le)
          _ = _ := (add_mul _ _ _).symm

#print axioms exists_second_directional_source_bound
end Yamabe3.Analysis.UniformElliptic
