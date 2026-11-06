import Yamabe3.Analysis.CompactNeighborhoodPartition
import Yamabe3.Analysis.BoundaryDifferentiatedSourceBound

/-! Quantitative finite patching of genuine local weak Sobolev functions.
All products are localized inside their actual regularity domains. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.BoundaryLocalization
variable {d : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ (Fin d)

def finitePhysicalPatch (ρ f : ι → E → ℝ) : E → ℝ := fun x => ∑ i, ρ i x*f i x

theorem finitePhysicalPatch_eq_on {N : ι → Set E} {U O : Set E}
    (ρ f : ι → E → ℝ) (u : E → ℝ)
    (hs : ∀ i, tsupport (ρ i) ⊆ N i)
    (hpart : ∀ x ∈ U, ∑ i, ρ i x = 1)
    (heq : ∀ i, EqOn (f i) u (N i ∩ O)) :
    EqOn (finitePhysicalPatch ρ f) u (U ∩ O) := by
  classical
  intro x hx
  have hi (i : ι) : ρ i x*f i x = ρ i x*u x := by
    by_cases hn : x ∈ N i
    · rw [heq i ⟨hn,hx.2⟩]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht => hn (hs i ht)), zero_mul, zero_mul]
  change (∑ i, ρ i x*f i x) = u x
  simp_rw [hi]
  rw [← Finset.sum_mul, hpart x hx.1, one_mul]

theorem finitePhysicalPatch_compact (ρ f : ι → E → ℝ)
    (hc : ∀ i, HasCompactSupport (ρ i)) : HasCompactSupport (finitePhysicalPatch ρ f) := by
  classical
  have hh (s : Finset ι) : HasCompactSupport (fun x => ∑ i ∈ s, ρ i x*f i x) := by
    induction s using Finset.induction_on with
    | empty => simp [HasCompactSupport]
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hc a).mul_right.add ih
  exact hh Finset.univ

theorem exists_finitePhysicalPatch_bound (k : ℕ) (N : ι → Set E)
    (hN : ∀ i, IsOpen (N i)) (ρ : ι → E → ℝ)
    (hρ : ∀ i, ContDiff ℝ ∞ (ρ i)) (hc : ∀ i, HasCompactSupport (ρ i))
    (hs : ∀ i, tsupport (ρ i) ⊆ N i) :
    ∃ C : ι → ℝ≥0∞, (∀ i, C i ≠ ⊤) ∧ ∀ f : ι → E → ℝ,
      (∀ i, MemWkp k 2 (f i) (N i)) →
      MemWkp k 2 (finitePhysicalPatch ρ f) univ ∧
      iteratedWeakSobolevNorm k 2 (finitePhysicalPatch ρ f) univ ≤
        ∑ i, C i * iteratedWeakSobolevNorm k 2 (f i) (N i) := by
  classical
  choose C hC hb using fun i => exists_localized_sobolev_multiplier_bound k isOpen_univ (hN i)
    (ρ i) (hρ i) (hc i) (hs i)
  refine ⟨C,hC,?_⟩
  intro f hf
  have hi (i : ι) : MemWkp k 2 (fun x => ρ i x*f i x) univ :=
    memWkp_mul_smooth_of_tsupport_subset k isOpen_univ (hN i)
      (by simpa only [inter_univ] using hf i) (hρ i) (hc i) (hs i)
  have hh := finite_sobolev_sum_with_bound isOpen_univ k Finset.univ
    (fun i x => ρ i x*f i x) (fun i _ => hi i)
  refine ⟨hh.1, hh.2.trans ?_⟩
  apply Finset.sum_le_sum
  intro i _
  simpa only [inter_univ] using hb i (f i) (by simpa only [inter_univ] using hf i)

#print axioms finitePhysicalPatch_eq_on
#print axioms exists_finitePhysicalPatch_bound
end Yamabe3.Analysis.UniformElliptic
