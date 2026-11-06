import Yamabe3.Analysis.EuclideanChartAE

/-! Local a.e. identities on actual precompact neighborhoods cover the
whole open domain by second countability. This does not infer anything
on the boundary of that domain. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped Topology
namespace Yamabe3.Analysis.UniformElliptic
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem ae_eq_restrict_of_precompact_local {O : Set E} (hO : IsOpen O) {f g : E → ℝ}
    (hlocal : ∀ W : Set E,IsOpen W → IsCompact (closure W) → closure W⊆O →
      f =ᵐ[volume.restrict W] g) : f =ᵐ[volume.restrict O] g := by
  classical
  have hex (x : O) : ∃W : Set E,IsOpen W ∧ (x:E)∈W ∧ closure W⊆O ∧ IsCompact (closure W) := by
    obtain ⟨W,hW,hxW,hWO,hWc⟩ := exists_open_between_and_isCompact_closure
      (isCompact_singleton (x:=(x:E))) hO (singleton_subset_iff.mpr x.2)
    exact ⟨W,hW,hxW (mem_singleton _),hWO,hWc⟩
  choose W hW hxW hWO hWc using hex
  obtain ⟨T,hT,hTc⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  have hcover : O⊆⋃x∈T,W x := by
    rw [hTc]
    exact fun y hy => mem_iUnion.mpr ⟨⟨y,hy⟩,hxW ⟨y,hy⟩⟩
  exact ae_restrict_of_ae_restrict_of_subset hcover
    ((ae_eq_restrict_biUnion_iff W hT _ _).mpr (fun x _ => hlocal (W x) (hW x) (hWc x) (hWO x)))

#print axioms ae_eq_restrict_of_precompact_local
end Yamabe3.Analysis.UniformElliptic
