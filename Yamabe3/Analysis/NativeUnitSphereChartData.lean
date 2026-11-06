import Yamabe3.Analysis.NativeUnitSphereChart
import Yamabe3.Analysis.BoundaryChartPotentialH4

/-! Source-independent compact chart data at each unit-sphere point. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology Manifold
namespace Yamabe3.Analysis.UniformElliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_unitSphere_chart_data (a : E) (ha : ‖a‖ = 1) :
    ∃ (e : OpenPartialHomeomorph E E) (χ : E → ℝ) (W V : Set E),
      a ∈ e.target ∧ e.target ⊆ halfEndSourceAnnulus ∧ e.symm a ∈ V ∧
      IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ e.source ∧
      IsOpen V ∧ IsCompact (closure V) ∧ closure V ⊆ W ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ e.target ∧ (∀ x ∈ W, χ (e x) = 1) ∧
      (∀ x ∈ e.source, e x ∈ (Metric.ball (0 : E) 1 \ {(0 : E)}) ↔ 0 < x 0) := by
  obtain ⟨e, hae, het, he, hei, hflat, -⟩ := exists_unitSphere_flattening_chart a ha
  obtain ⟨χ, -, hχs⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 3) a).mem_iff.mp
    (e.open_target.mem_nhds hae)
  have heLim : Tendsto e (𝓝 (e.symm a)) (𝓝 a) := by
    simpa only [e.right_inv hae] using (e.continuousAt (e.map_target hae)).tendsto
  have hχe : (fun x => χ (e x)) =ᶠ[𝓝 (e.symm a)] 1 := χ.eventuallyEq_one.comp_tendsto heLim
  obtain ⟨T, hTsub, hT, hxT⟩ := mem_nhds_iff.mp hχe
  obtain ⟨W, hW, hxW, hWsT, hWc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm a)) (e.open_source.inter hT)
    (singleton_subset_iff.mpr ⟨e.map_target hae, hxT⟩)
  obtain ⟨V, hV, hxV, hVW, hVc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm a)) hW hxW
  exact ⟨e, χ, W, V, hae, het, hxV (mem_singleton _), hW, hWc,
    hWsT.trans inter_subset_left, hV, hVc, hVW, he, hei, χ.contMDiff, χ.hasCompactSupport,
    hχs, fun x hx => hTsub (hWsT (subset_closure hx)).2, hflat⟩

#print axioms exists_unitSphere_chart_data
end Yamabe3.Analysis.UniformElliptic
