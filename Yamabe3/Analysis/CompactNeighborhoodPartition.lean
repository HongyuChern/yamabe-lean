import Yamabe3.Analysis.BoundaryPhysicalLocalExtension
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! A finite smooth partition on an open neighborhood of a compact set,
subordinate to the supplied actual neighborhoods. Equality of the sum is
proved on a neighborhood, not merely on the boundary set. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped ContDiff Topology Manifold
namespace Yamabe3.Analysis.UniformElliptic
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_finite_neighborhood_partition {K : Set E} (hK : IsCompact K)
    (N : K → Set E) (hN : ∀ a, IsOpen (N a)) (haN : ∀ a : K, (a : E) ∈ N a) :
    ∃ (s : Finset K) (U : Set E) (ρ : s → E → ℝ),
      IsOpen U ∧ K ⊆ U ∧
      (∀ i, ContDiff ℝ ∞ (ρ i)) ∧
      (∀ i, HasCompactSupport (ρ i)) ∧
      (∀ i, tsupport (ρ i) ⊆ N i.1) ∧
      (∀ x ∈ U, ∑ i, ρ i x = 1) := by
  classical
  choose b hb0 hb using fun a : K =>
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 d) (a : E)).mem_iff.mp
      ((hN a).mem_nhds (haN a))
  let W (a : K) : Set E := {x | (b a : E → ℝ) =ᶠ[𝓝 x] 1}
  have hW (a : K) : IsOpen (W a) := isOpen_setOf_eventually_nhds
  have hcover : K ⊆ ⋃ a : K, W a := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, (b ⟨x,hx⟩).eventuallyEq_one⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover W hW hcover
  let U : Set E := ⋃ i : s, W i.1
  have hU : IsOpen U := isOpen_iUnion (fun i => hW i.1)
  have hKU : K ⊆ U := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,hax⟩
  let B : BumpCovering s E U :=
    { toFun := fun i => ⟨b i.1, (b i.1).continuous⟩
      locallyFinite' := locallyFinite_of_finite _
      nonneg' := fun i x => ((b i.1).mem_Icc).1
      le_one' := fun i x => ((b i.1).mem_Icc).2
      eventuallyEq_one' := fun x hx => by
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact ⟨i,hi⟩ }
  let ρ := B.toSmoothPartitionOfUnity (fun i => (b i.1).contMDiff)
  have hsup (i : s) : tsupport (ρ i : E → ℝ) ⊆ tsupport (b i.1 : E → ℝ) :=
    closure_mono (B.support_toPartitionOfUnity_subset i)
  refine ⟨s, U, fun i => ρ i, hU, hKU, fun i => (ρ i).contMDiff.contDiff,
    fun i => (b i.1).hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (hsup i),
    fun i => (hsup i).trans (hb i.1), ?_⟩
  intro x hx
  simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx

#print axioms exists_finite_neighborhood_partition
end Yamabe3.Analysis.UniformElliptic
