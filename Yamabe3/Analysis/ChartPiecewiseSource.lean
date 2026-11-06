import Yamabe3.Analysis.FlatSplitSource
import Yamabe3.Analysis.NativeWeakChartDivergence

/-! The actual two physical source pieces become the corresponding two
coordinate pieces. Values on the flat face are removed only by its proved
volume-nullness, never by restricting a volume identity to a boundary. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology Manifold
namespace Yamabe3.Analysis.UniformElliptic
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem euclidean_coordinate_ne_zero_ae (i : Fin d) :
    ∀ᵐ x : E ∂volume,x i≠0 := by
  have h : ∀ᵐ y : Fin d → ℝ ∂volume,y i≠0 := Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i 0
  exact (PiLp.volume_preserving_ofLp (Fin d)).quasiMeasurePreserving.tendsto_ae.eventually h

def physicalSplitSource (Ω : Set E) (f g : E → ℝ) : E → ℝ := by
  classical
  exact Ω.piecewise f g

theorem weighted_chart_piecewise_eq
    {O Ω : Set E} (hO : IsOpen O) (e : E → E)
    (hflat : ∀ x∈O,e x∈Ω ↔ 0<x 0) (σ f g : E → ℝ) :
    (fun x => σ x*physicalSplitSource Ω f g (e x)) =ᵐ[volume.restrict O]
      flatSplitSource (fun x => σ x*f (e x)) (fun x => σ x*g (e x)) := by
  classical
  filter_upwards [ae_restrict_mem hO.measurableSet,
    ae_restrict_of_ae (euclidean_coordinate_ne_zero_ae (0:Fin d))] with x hx hn
  by_cases hp : 0<x 0
  · have he := (hflat x hx).mpr hp
    simp only [physicalSplitSource,piecewise_eq_of_mem Ω f g he,flatSplitSource,if_pos hp]
  · have he : e x∉Ω := fun h => hp ((hflat x hx).mp h)
    have hm : x 0<0 := lt_of_le_of_ne (le_of_not_gt hp) hn
    simp only [physicalSplitSource,piecewise_eq_of_notMem Ω f g he,flatSplitSource,if_neg hp,if_pos hm]

#print axioms euclidean_coordinate_ne_zero_ae
#print axioms weighted_chart_piecewise_eq
end Yamabe3.Analysis.UniformElliptic
