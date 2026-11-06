import Yamabe3.Analysis.SobolevLocalPullback
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.L2Pullback
import PoincareLib.Geometry.Riemannian.Measure.Euclidean

/-! A genuine smooth Euclidean chart produces both the change-of-measure
bound and the density-weighted source estimate, from the original Hk input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology Manifold
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_euclidean_chart_source_bound (k : ℕ)
    (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 d) (𝓡 d) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 d) (𝓡 d) ∞ e.symm e.target)
    {O W : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOs : closure O ⊆ e.source) (hW : IsOpen W) (heW : e '' closure O ⊆ W) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : E → ℝ, MemWkp k 2 u W →
      MemWkp k 2 (fun x => u (e x)) O ∧
      iteratedWeakSobolevNorm k 2 (fun x => u (e x)) O ≤ C * iteratedWeakSobolevNorm k 2 u W := by
  obtain ⟨c, hc, hK⟩ := (RiemannianMetric.euclideanMetric d).exists_map_compact_coordinate_le e he hei hOc hOs
  have hmeas : AEMeasurable e (volume.restrict (closure O)) :=
    (e.continuousOn.mono hOs).aemeasurable isClosed_closure.measurableSet
  have hmap : (volume.restrict O).map e ≤ c • volume := by
    exact (Measure.map_mono_of_aemeasurable (Measure.restrict_mono_set volume subset_closure) hmeas).trans
      (by simpa only [RiemannianMetric.euclideanMetric_volumeMeasure] using hK)
  exact exists_local_source_pullback_bound k hO hOc e.open_source hOs hW e he.contDiffOn heW c hc hmap

/-- The source of the weak coordinate equation is the actual physical
source times the actual pullback volume density, with all Hk and norm
claims produced from physical Hk. -/
theorem exists_euclidean_chart_density_source_bound (k : ℕ)
    (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 d) (𝓡 d) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 d) (𝓡 d) ∞ e.symm e.target)
    {O W : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOs : closure O ⊆ e.source) (hW : IsOpen W) (heW : e '' closure O ⊆ W) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : E → ℝ, MemWkp k 2 u W →
      MemWkp k 2 (fun x => (RiemannianMetric.euclideanMetric d).pullbackVolumeDensity e x * u (e x)) O ∧
      iteratedWeakSobolevNorm k 2
        (fun x => (RiemannianMetric.euclideanMetric d).pullbackVolumeDensity e x * u (e x)) O ≤
          C * iteratedWeakSobolevNorm k 2 u W := by
  let g := RiemannianMetric.euclideanMetric d
  have hD : e.MDifferentiable (𝓡 d) (𝓡 d) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContDiffOn ℝ ∞ (g.pullbackVolumeDensity e) e.source := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hx)) (hD.mfderiv_injective hx)).1.contDiffWithinAt
  obtain ⟨Cp, hCp, hp⟩ := exists_euclidean_chart_source_bound k e he hei hO hOc hOs hW heW
  obtain ⟨Cm, hCm, hm⟩ := exists_local_sobolev_multiplier_bound k hO hOc e.open_source hOs
    (g.pullbackVolumeDensity e) hρ
  refine ⟨Cm*Cp, ENNReal.mul_ne_top hCm hCp, ?_⟩
  intro u hu
  have hp' := hp u hu
  have hm' := hm (fun x => u (e x)) hp'.1
  refine ⟨hm'.1, ?_⟩
  exact hm'.2.trans (by simpa only [mul_assoc] using mul_le_mul le_rfl hp'.2 zero_le zero_le)

#print axioms exists_euclidean_chart_source_bound
#print axioms exists_euclidean_chart_density_source_bound
end Yamabe3.Analysis.UniformElliptic
