import Yamabe3.Analysis.SobolevEuclideanChart

/-! Actual coordinate maps preserve volume-a.e. equality on their source.
A countable open cover by precompact coordinate neighborhoods removes the
compact-set restriction of the pinned measure-change theorem. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped ENNReal Topology Manifold ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open PoincareMT.LeviCivitaData.Dirichlet
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem euclidean_chart_comp_congr_ae
    (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 d) (𝓡 d) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 d) (𝓡 d) ∞ e.symm e.target)
    {u v : E → ℝ} (huv : u =ᵐ[volume] v) :
    (fun x => u (e x)) =ᵐ[volume.restrict e.source] fun x => v (e x) := by
  classical
  have hex (a : e.source) : ∃ N : Set E, IsOpen N ∧ (a:E) ∈ N ∧
      closure N ⊆ e.source ∧ IsCompact (closure N) := by
    obtain ⟨N,hN,haN,hNs,hNc⟩ := exists_open_between_and_isCompact_closure
      (isCompact_singleton (x := (a:E))) e.open_source (singleton_subset_iff.mpr a.2)
    exact ⟨N,hN,haN (mem_singleton _),hNs,hNc⟩
  choose N hN haN hNs hNc using hex
  have hcover : e.source ⊆ ⋃ a : e.source, N a := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,haN ⟨x,hx⟩⟩
  obtain ⟨T,hT,hTcover⟩ := TopologicalSpace.isOpen_iUnion_countable N hN
  have hcover' : e.source ⊆ ⋃ a ∈ T, N a := by rwa [hTcover]
  have hn (a : e.source) : (fun x => u (e x)) =ᵐ[volume.restrict (N a)] fun x => v (e x) := by
    have hh := (RiemannianMetric.euclideanMetric d).ae_comp_on_compact e he hei (hNc a) (hNs a)
      (by simpa only [RiemannianMetric.euclideanMetric_volumeMeasure] using huv)
    exact ae_restrict_of_ae_restrict_of_subset subset_closure hh
  exact ae_restrict_of_ae_restrict_of_subset hcover'
    ((ae_eq_restrict_biUnion_iff N hT _ _).mpr (fun a _ => hn a))

theorem euclidean_chartPullback_congr_ae
    (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 d) (𝓡 d) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 d) (𝓡 d) ∞ e.symm e.target)
    {u v : E → ℝ} (huv : u =ᵐ[volume] v) :
    chartPullback e u =ᵐ[volume] chartPullback e v := by
  have hh := (ae_restrict_iff' e.open_source.measurableSet).mp (euclidean_chart_comp_congr_ae e he hei huv)
  filter_upwards [hh] with x hx
  by_cases hxs : x ∈ e.source
  · simpa only [chartPullback_apply e _ hxs] using hx hxs
  · simp [chartPullback,hxs]

#print axioms euclidean_chart_comp_congr_ae
#print axioms euclidean_chartPullback_congr_ae
end Yamabe3.Analysis.UniformElliptic
