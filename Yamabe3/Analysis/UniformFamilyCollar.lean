import Yamabe3.Analysis.CompactSobolevPatching

/-! Finite geometric patching of a whole family with one constant before
all family parameters. The overlap identity is pointwise with the same
input function. No solver is assumed by this patching lemma. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_uniform_family_compact_collar {J : Type*} (k : ℕ)
    (Ω K : Set E) (hK : IsCompact K) (u : J → E → ℝ) (B : J → ℝ≥0∞)
    (hlocal : ∀ a ∈ K, ∃ (N : Set E) (L : J → E → ℝ) (C : ℝ≥0∞),
      a ∈ N ∧ IsOpen N ∧ C ≠ ⊤ ∧
      ∀ j, MemWkp k 2 (L j) N ∧
        iteratedWeakSobolevNorm k 2 (L j) N ≤ C*B j ∧
        EqOn (L j) (u j) (N ∩ Ω)) :
    ∃ (U : Set E) (L : J → E → ℝ) (C : ℝ≥0∞),
      IsOpen U ∧ K ⊆ U ∧ C ≠ ⊤ ∧
      ∀ j, HasCompactSupport (L j) ∧ MemWkp k 2 (L j) univ ∧
        iteratedWeakSobolevNorm k 2 (L j) univ ≤ C*B j ∧
        EqOn (L j) (u j) (U ∩ Ω) := by
  classical
  choose N L C haN hN hC hl using fun a : K => hlocal a a.2
  obtain ⟨s,U,ρ,hU,hKU,hρ,hρc,hρs,hpart⟩ :=
    exists_finite_neighborhood_partition hK N hN haN
  obtain ⟨D,hD,hb⟩ := exists_finitePhysicalPatch_bound k (fun i : s => N i.1)
    (fun i => hN i.1) ρ hρ hρc hρs
  let T (j : J) := finitePhysicalPatch ρ (fun i : s => L i.1 j)
  refine ⟨U,T,∑ i : s, D i*C i.1,hU,hKU,
    ENNReal.sum_ne_top.mpr (fun i _ => ENNReal.mul_ne_top (hD i) (hC i.1)),?_⟩
  intro j
  have hh := hb (fun i : s => L i.1 j) (fun i => (hl i.1 j).1)
  refine ⟨finitePhysicalPatch_compact ρ _ hρc,hh.1,hh.2.trans ?_,?_⟩
  · calc
      _ ≤ ∑ i : s, D i*(C i.1*B j) := Finset.sum_le_sum (fun i _ =>
        mul_le_mul le_rfl (hl i.1 j).2.1 zero_le zero_le)
      _ = _ := by simp only [Finset.sum_mul,mul_assoc]
  · exact finitePhysicalPatch_eq_on ρ (fun i : s => L i.1 j) (u j) hρs hpart
      (fun i => (hl i.1 j).2.2)

#print axioms exists_uniform_family_compact_collar
end Yamabe3.Analysis.UniformElliptic
