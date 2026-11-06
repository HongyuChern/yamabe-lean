import Yamabe3.Analysis.EuclideanChartAE

/-! Restricted a.e. identities transport through the actual smooth chart.
Zero extension supplies a global a.e. identity; the retained chart domain
then removes the extension without restricting any volume identity to a surface. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped ENNReal Topology Manifold ContDiff
namespace Yamabe3.Analysis.UniformElliptic
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem euclidean_chart_comp_congr_ae_restrict
    (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 d) (𝓡 d) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 d) (𝓡 d) ∞ e.symm e.target)
    {O W : Set E} (hO : IsOpen O) (hW : IsOpen W)
    (hOs : O ⊆ e.source) (heW : MapsTo e O W)
    {u v : E → ℝ} (huv : u =ᵐ[volume.restrict W] v) :
    (fun x => u (e x)) =ᵐ[volume.restrict O] fun x => v (e x) := by
  classical
  have hz : W.indicator u =ᵐ[volume] W.indicator v := by
    filter_upwards [(ae_restrict_iff' hW.measurableSet).mp huv] with x hx
    by_cases h : x ∈ W
    · simp only [indicator_of_mem h, hx h]
    · simp only [indicator_of_notMem h]
  have ht := ae_restrict_of_ae_restrict_of_subset hOs
    (euclidean_chart_comp_congr_ae e he hei hz)
  filter_upwards [ht, ae_restrict_mem hO.measurableSet] with x hx hxo
  simpa only [indicator_of_mem (heW hxo)] using hx

#print axioms euclidean_chart_comp_congr_ae_restrict
end Yamabe3.Analysis.UniformElliptic
