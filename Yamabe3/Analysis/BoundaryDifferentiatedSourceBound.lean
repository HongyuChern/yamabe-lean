import Yamabe3.Analysis.BoundarySobolevMultiplier
import Yamabe3.Analysis.BoundaryWeakSourceBootstrap

/-! Retain quantitative bounds for the explicitly constructed differentiated
source. The equation and signs use the fixed differentiated weak equation.
The construction refines S014 BoundaryWeakSourceBootstrap without changing it. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryTangential
open Poincare.Analysis.Sobolev.BoundaryLocalization
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem finite_sobolev_sum_with_bound {O : Set E} (hO : IsOpen O) (k : ℕ)
    {I : Type*} (s : Finset I) (v : I → E → ℝ)
    (hv : ∀ i ∈ s, MemWkp k 2 (v i) O) :
    MemWkp k 2 (fun x => ∑ i ∈ s, v i x) O ∧
      iteratedWeakSobolevNorm k 2 (fun x => ∑ i ∈ s, v i x) O ≤
        ∑ i ∈ s, iteratedWeakSobolevNorm k 2 (v i) O := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using And.intro (MemWkp_zero_fun (d := d) (k := k) (by norm_num) hO)
      (le_of_eq (wkpNorm_zero_fun_zero (d := d) (k := k) (by norm_num) hO))
  | @insert a s ha ih =>
    have hs := ih (fun i hi => hv i (Finset.mem_insert_of_mem hi))
    have h1 := hv a (Finset.mem_insert_self a s)
    simp only [Finset.sum_insert ha]
    exact ⟨MemWkp.add (by norm_num) hO h1 hs.1,
      (wkpNorm_add_le (by norm_num) hO h1 hs.1).trans (add_le_add le_rfl hs.2)⟩

/-- For every fixed coefficient/domain, all commutator constants are fixed
before the source and solution. The produced F is the differentiated source
of the original equation, and its Hk norm is controlled by f H(k+1) and
u H(k+2). This is an auxiliary estimate, not an assumed derivative PDE. -/
theorem exists_differentiated_source_uniform_bound
    (k : ℕ) {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (a : E → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j)) (l : Fin d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (u f : E → ℝ),
      MemWkp (k+2) 2 u O → MemWkp (k+1) 2 f O →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
        (∫ x in O, ∑ i, ∑ j, a x i j * chosenWeakPartial' 2 j u O x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x) →
      ∃ F : E → ℝ, MemWkp k 2 F O ∧
        iteratedWeakSobolevNorm k 2 F O ≤ iteratedWeakSobolevNorm (k+1) 2 f O +
          C * iteratedWeakSobolevNorm (k+2) 2 u O ∧
        ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
          (∫ x in O, ∑ i, ∑ j, a x i j *
            chosenWeakPartial' 2 j (chosenWeakPartial' 2 l u O) O x *
            fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, F x * φ x := by
  classical
  let da (i j : Fin d) (x : E) := fderiv ℝ (fun y => a y i j) x (EuclideanSpace.single l 1)
  let dda (i j : Fin d) (x : E) := fderiv ℝ (da i j) x (EuclideanSpace.single i 1)
  have hda (i j : Fin d) : ContDiff ℝ ∞ (da i j) :=
    ((ha i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdda (i j : Fin d) : ContDiff ℝ ∞ (dda i j) :=
    ((hda i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  choose A hA hbA using fun i j => exists_compact_sobolev_multiplier_bound k hO hOc (da i j) (hda i j)
  choose B hB hbB using fun i j => exists_compact_sobolev_multiplier_bound k hO hOc (dda i j) (hdda i j)
  let C : ℝ≥0∞ := ∑ i, ∑ j, (B i j + A i j)
  have hC : C ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => ENNReal.sum_ne_top.mpr fun j _ =>
    ENNReal.add_ne_top.mpr ⟨hB i j, hA i j⟩
  refine ⟨C, hC, ?_⟩
  intro u f hu hf heq
  let p (j : Fin d) := chosenWeakPartial' 2 j u O
  let q (i j : Fin d) := chosenWeakPartial' 2 j (p i) O
  let r := chosenWeakPartial' 2 l f O
  let G (i j : Fin d) (x : E) := dda i j x * p j x + da i j x * q i j x
  let F : E → ℝ := fun x => r x + ∑ i, ∑ j, G i j x
  have hp (i : Fin d) : MemWkp (k+1) 2 (p i) O := hu.chosenWeakPartial_mem i
  have hq (i j : Fin d) : MemWkp k 2 (q i j) O := (hp i).chosenWeakPartial_mem j
  have hG (i j : Fin d) : MemWkp k 2 (G i j) O := MemWkp.add (by norm_num) hO
    (memWkp_mul_smooth_of_isCompact_closure k hO hOc (hp j).le_succ (hdda i j))
    (memWkp_mul_smooth_of_isCompact_closure k hO hOc (hq i j) (hda i j))
  have hsum := finite_sobolev_sum_with_bound hO k Finset.univ (fun i x => ∑ j, G i j x)
    (fun i _ => (finite_sobolev_sum_with_bound hO k Finset.univ (G i) (fun j _ => hG i j)).1)
  have hF : MemWkp k 2 F O := MemWkp.add (by norm_num) hO (hf.chosenWeakPartial_mem l) hsum.1
  have hpn (i : Fin d) : iteratedWeakSobolevNorm k 2 (p i) O ≤ iteratedWeakSobolevNorm (k+2) 2 u O :=
    (Poincare.Analysis.Sobolev.Euclidean.wkpNorm_mono_order (Nat.le_succ k) (p i) O).trans
      (wkpNorm_chosenWeakPartial_le_wkpNorm_succ (k+1) 2 u O i)
  have hqn (i j : Fin d) : iteratedWeakSobolevNorm k 2 (q i j) O ≤ iteratedWeakSobolevNorm (k+2) 2 u O :=
    (wkpNorm_chosenWeakPartial_le_wkpNorm_succ k 2 (p i) O j).trans
      (wkpNorm_chosenWeakPartial_le_wkpNorm_succ (k+1) 2 u O i)
  have hGn (i j : Fin d) : iteratedWeakSobolevNorm k 2 (G i j) O ≤
      (B i j + A i j) * iteratedWeakSobolevNorm (k+2) 2 u O := by
    calc
      _ ≤ iteratedWeakSobolevNorm k 2 (fun x => dda i j x * p j x) O +
          iteratedWeakSobolevNorm k 2 (fun x => da i j x * q i j x) O :=
        wkpNorm_add_le (by norm_num) hO
          (memWkp_mul_smooth_of_isCompact_closure k hO hOc (hp j).le_succ (hdda i j))
          (memWkp_mul_smooth_of_isCompact_closure k hO hOc (hq i j) (hda i j))
      _ ≤ B i j * iteratedWeakSobolevNorm k 2 (p j) O + A i j * iteratedWeakSobolevNorm k 2 (q i j) O :=
        add_le_add (hbB i j _ (hp j).le_succ) (hbA i j _ (hq i j))
      _ ≤ B i j * iteratedWeakSobolevNorm (k+2) 2 u O + A i j * iteratedWeakSobolevNorm (k+2) 2 u O := by
          apply add_le_add
          · exact mul_le_mul le_rfl (hpn j) zero_le zero_le
          · exact mul_le_mul le_rfl (hqn i j) zero_le zero_le
      _ = _ := (add_mul _ _ _).symm
  refine ⟨F, hF, ?_, ?_⟩
  · calc
      _ ≤ iteratedWeakSobolevNorm k 2 r O + iteratedWeakSobolevNorm k 2 (fun x => ∑ i, ∑ j, G i j x) O :=
        wkpNorm_add_le (by norm_num) hO (hf.chosenWeakPartial_mem l) hsum.1
      _ ≤ iteratedWeakSobolevNorm (k+1) 2 f O + ∑ i, ∑ j, iteratedWeakSobolevNorm k 2 (G i j) O :=
        add_le_add (wkpNorm_chosenWeakPartial_le_wkpNorm_succ k 2 f O l)
          (hsum.2.trans (Finset.sum_le_sum fun i _ =>
            (finite_sobolev_sum_with_bound hO k Finset.univ (G i) (fun j _ => hG i j)).2))
      _ ≤ iteratedWeakSobolevNorm (k+1) 2 f O + ∑ i, ∑ j,
          (B i j + A i j) * iteratedWeakSobolevNorm (k+2) 2 u O := by gcongr with i _ j _; exact hGn i j
      _ = _ := by simp only [C, Finset.sum_mul]
  · have hw (i j : Fin d) : HasWeakPartialDeriv i (q i j) (p j) O := weakPartial_commute i j
        (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i)
        (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p j)
        (chosenWeakPartial'_isWeakPartial_of_mem (hp i).memW1p j)
    exact (differentiated_weak_divergence hO hOc a ha l
      (fun i => (hp i).memLp) (fun i j => (hq i j).memLp) hw
      hf.memLp (hf.chosenWeakPartial_mem l).memLp
      (chosenWeakPartial'_isWeakPartial_of_mem hf.memW1p l) heq).2

#print axioms finite_sobolev_sum_with_bound
#print axioms exists_differentiated_source_uniform_bound
end Yamabe3.Analysis.UniformElliptic
