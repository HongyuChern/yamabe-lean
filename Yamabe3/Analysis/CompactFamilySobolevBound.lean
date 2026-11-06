import Yamabe3.Analysis.UniformFamilyCollar

/-! A finite cover turns parameter-uniform local bounds for the same
function into a bound on a fixed precompact domain. The cutoff patch
agrees with the actual input; it does not choose independent solutions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped ENNReal ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_compact_family_sobolev_bound {J : Type*} (k : ℕ)
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (u : J → E → ℝ) (B : J → ℝ≥0∞)
    (hl : ∀ a ∈ closure V, ∃ (N : Set E) (C : ℝ≥0∞),
      a ∈ N ∧ IsOpen N ∧ C ≠ ⊤ ∧ ∀ j,
        MemWkp k 2 (u j) N ∧ iteratedWeakSobolevNorm k 2 (u j) N ≤ C*B j) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ j, MemWkp k 2 (u j) V ∧
      iteratedWeakSobolevNorm k 2 (u j) V ≤ C*B j := by
  have hlocal : ∀ a ∈ closure V, ∃ (N : Set E) (L : J → E → ℝ) (C : ℝ≥0∞),
      a ∈ N ∧ IsOpen N ∧ C ≠ ⊤ ∧ ∀ j,
        MemWkp k 2 (L j) N ∧ iteratedWeakSobolevNorm k 2 (L j) N ≤ C*B j ∧
          EqOn (L j) (u j) (N ∩ univ) := by
    intro a ha
    obtain ⟨N,C,haN,hN,hC,hb⟩ := hl a ha
    exact ⟨N,u,C,haN,hN,hC,fun j => ⟨(hb j).1,(hb j).2,fun _ _ => rfl⟩⟩
  obtain ⟨U,L,C,hU,hVU,hC,hb⟩ := exists_uniform_family_compact_collar k univ
    (closure V) hVc u B hlocal
  refine ⟨C,hC,?_⟩
  intro j
  have hj := hb j
  have hae : L j =ᵐ[volume.restrict V] u j := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    exact hj.2.2.2 ⟨hVU (subset_closure hx),mem_univ x⟩
  refine ⟨(MemWkp_congr_ae (by norm_num) hV hae).mp
    (hj.2.1.mono_set (by norm_num) hV (subset_univ V)),?_⟩
  rw [← wkpNorm_congr_ae (k := k) (by norm_num) hV hae]
  exact (wkpNorm_mono_set (by norm_num) hV (subset_univ V) hj.2.1).trans hj.2.2.1

#print axioms exists_compact_family_sobolev_bound
end Yamabe3.Analysis.UniformElliptic
