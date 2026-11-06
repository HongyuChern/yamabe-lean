import Yamabe3.Analysis.WeakMultiplierExplicit
import Yamabe3.Analysis.WeakLaplacianSobolev
import Yamabe3.Analysis.UniformElliptic.NativeSmallGeometricError

/-! The literal weak second-order error is bounded from actual H4 to H2.
The bound is linear in the coefficient jets, also for nonsmooth H4 inputs.
This is a local operator bound; graph realization and low-mode closure
remain separate obligations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryLocalization
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
local notation "E" => EuclideanSpace ℝ (Fin 3)

def weakSecondOrderPerturbation (O : Set E)
    (a : Fin 3 → Fin 3 → E → ℝ) (b : Fin 3 → E → ℝ) (c u : E → ℝ) : E → ℝ :=
  fun x => (∑ i : Fin 3, ∑ j : Fin 3,
    a i j x * chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u O) O x) +
    (∑ j : Fin 3, b j x * chosenWeakPartial' 2 j u O x) + c x * u x

theorem weakSecondOrderPerturbation_mem_bound {O : Set E}
    (hO : IsOpen O) (hOc : IsCompact (closure O)) {η : ℝ} (hη : 0 ≤ η)
    (a : Fin 3 → Fin 3 → E → ℝ) (b : Fin 3 → E → ℝ) (c u : E → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hb : ∀ j, ContDiff ℝ ∞ (b j))
    (hc : ContDiff ℝ ∞ c) (hu : MemWkp 4 2 u O)
    (haj : ∀ n ≤ 2, ∀ x ∈ O, ∀ i j, ‖iteratedFDeriv ℝ n (a i j) x‖ ≤ η)
    (hbj : ∀ n ≤ 2, ∀ x ∈ O, ∀ j, ‖iteratedFDeriv ℝ n (b j) x‖ ≤ η)
    (hcj : ∀ n ≤ 2, ∀ x ∈ O, ‖iteratedFDeriv ℝ n c x‖ ≤ η) :
    MemWkp 2 2 (weakSecondOrderPerturbation O a b c u) O ∧
      iteratedWeakSobolevNorm 2 2 (weakSecondOrderPerturbation O a b c u) O ≤
        ENNReal.ofReal (637*η)*iteratedWeakSobolevNorm 4 2 u O := by
  classical
  let N := iteratedWeakSobolevNorm 4 2 u O
  let K : ℝ≥0∞ := 49*ENNReal.ofReal η
  have hmul (q v : E → ℝ) (hq : ContDiff ℝ ∞ q)
      (hqj : ∀ n ≤ 2, ∀ x ∈ O, ‖iteratedFDeriv ℝ n q x‖ ≤ η)
      (hv : MemWkp 2 2 v O) (hvN : iteratedWeakSobolevNorm 2 2 v O ≤ N) :
      MemWkp 2 2 (fun x => q x*v x) O ∧
        iteratedWeakSobolevNorm 2 2 (fun x => q x*v x) O ≤ K*N := by
    refine ⟨memWkp_mul_smooth_of_isCompact_closure 2 hO hOc hv hq,?_⟩
    have hh := weak_sobolev_multiplier_explicit_bound 2 hO hOc hη q hq hqj v hv
    norm_num at hh
    exact hh.trans (mul_le_mul le_rfl hvN zero_le zero_le)
  let A (i j : Fin 3) := fun x => a i j x * chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u O) O x
  let B (j : Fin 3) := fun x => b j x * chosenWeakPartial' 2 j u O x
  have hA (i j : Fin 3) : MemWkp 2 2 (A i j) O ∧ iteratedWeakSobolevNorm 2 2 (A i j) O ≤ K*N :=
    hmul _ _ (ha i j) (fun n hn x hx => haj n hn x hx i j)
      ((hu.chosenWeakPartial_mem j).chosenWeakPartial_mem i)
      ((wkpNorm_chosenWeakPartial_le_wkpNorm_succ 2 2 (chosenWeakPartial' 2 j u O) O i).trans
        (wkpNorm_chosenWeakPartial_le_wkpNorm_succ 3 2 u O j))
  have hB (j : Fin 3) : MemWkp 2 2 (B j) O ∧ iteratedWeakSobolevNorm 2 2 (B j) O ≤ K*N :=
    hmul _ _ (hb j) (fun n hn x hx => hbj n hn x hx j)
      ((hu.chosenWeakPartial_mem j).le_succ)
      ((wkpNorm_mono_order (by omega : 2 ≤ 3) _ _).trans
        (wkpNorm_chosenWeakPartial_le_wkpNorm_succ 3 2 u O j))
  have hC := hmul c u hc hcj (hu.le_of_le (by omega)) (wkpNorm_mono_order (by omega : 2 ≤ 4) _ _)
  have hrow (i : Fin 3) := finite_sobolev_sum_with_bound hO 2 Finset.univ (A i) (fun j _ => (hA i j).1)
  have hsum := finite_sobolev_sum_with_bound hO 2 Finset.univ
    (fun i => fun x => ∑ j : Fin 3, A i j x) (fun i _ => (hrow i).1)
  have hfirst := finite_sobolev_sum_with_bound hO 2 Finset.univ B (fun j _ => (hB j).1)
  have hAB := MemWkp.add (by norm_num : (1:ℝ≥0∞) ≤ 2) hO hsum.1 hfirst.1
  refine ⟨MemWkp.add (by norm_num) hO hAB hC.1,?_⟩
  have haN : iteratedWeakSobolevNorm 2 2 (fun x => ∑ i : Fin 3, ∑ j : Fin 3, A i j x) O ≤ 9*(K*N) := by
    calc
      _ ≤ ∑ i : Fin 3, iteratedWeakSobolevNorm 2 2 (fun x => ∑ j : Fin 3, A i j x) O := hsum.2
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, K*N := Finset.sum_le_sum (fun i _ =>
        (hrow i).2.trans (Finset.sum_le_sum (fun j _ => (hA i j).2)))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]; ring
  have hbN : iteratedWeakSobolevNorm 2 2 (fun x => ∑ j : Fin 3, B j x) O ≤ 3*(K*N) := by
    exact hfirst.2.trans (by simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
      using Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => (hB j).2))
  have hh := (wkpNorm_add_le (by norm_num : (1:ℝ≥0∞) ≤ 2) hO hAB hC.1).trans
    (add_le_add ((wkpNorm_add_le (by norm_num) hO hsum.1 hfirst.1).trans (add_le_add haN hbN)) hC.2)
  apply hh.trans_eq
  dsimp only [K,N]
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 637),ENNReal.ofReal_ofNat]
  ring

#print axioms weakSecondOrderPerturbation_mem_bound
end Yamabe3.Analysis.UniformElliptic
