import Yamabe3.Analysis.CompactSobolevPatching
import PoincareLib.Analysis.Elliptic.Regularity.Iteration.LocalSobolev

/-! A genuine compact weak-Sobolev extension near a retained compact set.
It is assembled from the actual local witnesses; no regularity across the
boundary of the original domain is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_compact_sobolev_extension_near_compact
    {k : ℕ} {O K : Set E} {u : E → ℝ}
    (hu : MemWkpLocally k u O) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ (v : E → ℝ) (U : Set E),
      IsOpen U ∧ K ⊆ U ∧ HasCompactSupport v ∧ MemWkp k 2 v univ ∧ EqOn v u U := by
  classical
  choose N hN haN hNO huN using fun a : K => hu a (hKO a.2)
  obtain ⟨s,U,ρ,hU,hKU,hρ,hρc,hρs,hpart⟩ :=
    exists_finite_neighborhood_partition hK N hN haN
  obtain ⟨C,hC,hb⟩ := exists_finitePhysicalPatch_bound k (fun i : s => N i.1)
    (fun i => hN i.1) ρ hρ hρc hρs
  let v := finitePhysicalPatch ρ (fun _ : s => u)
  refine ⟨v,U,hU,hKU,finitePhysicalPatch_compact ρ _ hρc,
    (hb (fun _ : s => u) (fun i => huN i.1)).1, ?_⟩
  have hh := finitePhysicalPatch_eq_on (O := univ) ρ (fun _ : s => u) u hρs hpart
    (fun _ _ _ => rfl)
  simpa only [inter_univ] using hh

theorem memWkp_on_precompact_of_locally
    {k : ℕ} {O V : Set E} {u : E → ℝ}
    (hu : MemWkpLocally k u O) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O) : MemWkp k 2 u V := by
  obtain ⟨v,U,hU,hVU,hvc,hv,heq⟩ := exists_compact_sobolev_extension_near_compact hu hVc hVO
  apply (MemWkp_congr_ae (by norm_num) hV ?_).mp
    (hv.mono_set (by norm_num) hV (subset_univ _))
  filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
  exact heq (hVU (subset_closure hx))

#print axioms exists_compact_sobolev_extension_near_compact
#print axioms memWkp_on_precompact_of_locally
end Yamabe3.Analysis.UniformElliptic
