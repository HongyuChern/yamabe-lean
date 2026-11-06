import Yamabe3.Analysis.NativePrincipalErrorGraph
import Yamabe3.Analysis.NativePotentialErrorGraph

/-! The complete normalized native-minus-model differential error is an
actual small H4-to-H2 graph operator. The principal sign, scalar curvature,
density defect and Delaunay phase are retained. This does not yet assert
that its range is high, nor supply an inverse for its low component. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay
local notation "E" => EuclideanSpace ℝ (Fin 3)

def nativeNormalizedFullError (g : RiemannianMetric 3 E) (ε : ℝ)
    (v : ℝ → ℝ) (τ : ℝ) (u : E → ℝ) (x : E) : ℝ :=
  nativeNormalizedPotentialError g ε v τ u x-nativeNormalizedPrincipalError g ε u x

theorem exists_small_native_full_error_graph_operator
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0 = innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0 = 1)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ → ∀ a ∈ Λ,
      ∀ (κ : ℝ) (p : DelaunayPhaseData κ),
      ∃ T : HalfEndPhysicalH4Graph →L[ℝ] HalfEndPhysicalH2SourceGraph,
        ‖T‖ ≤ τ ∧ ∀ (v : HalfEndPhysicalH4Graph) (x : HalfEndSourceEntrance),
        halfEndPhysicalH2SourceGraphValue (T v) x = nativeNormalizedFullError (g a) ε p.orbit p.phase
          (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x := by
  obtain ⟨d,hd,hprincipal⟩ := exists_small_native_principal_error_graph_operator Λ g hB hρ (half_pos hτ)
  obtain ⟨e,he,hpotential⟩ := exists_small_native_potential_error_graph_operator Λ g hρ (half_pos hτ)
  refine ⟨min d e,lt_min hd he,?_⟩
  intro ε hε hεsmall a ha κ p
  obtain ⟨P,hP,hPv⟩ := hprincipal ε hε (hεsmall.trans_le (min_le_left _ _)) a ha
  obtain ⟨Q,hQ,hQv⟩ := hpotential ε hε (hεsmall.trans_le (min_le_right _ _)) a ha κ p
  refine ⟨Q-P,(norm_sub_le Q P).trans ((add_le_add hQ hP).trans_eq (by ring)),?_⟩
  intro v x
  change halfEndPhysicalH2SourceGraphValue (Q v-P v) x = _
  rw [map_sub]
  change halfEndPhysicalH2SourceGraphValue (Q v) x-halfEndPhysicalH2SourceGraphValue (P v) x = _
  rw [hQv,hPv]
  rfl

#print axioms exists_small_native_full_error_graph_operator
end Yamabe3.Analysis.UniformElliptic
