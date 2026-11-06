import Yamabe3.Analysis.BoundaryPhysicalLinearExtension
import Yamabe3.Analysis.NativeChartTransmissionH4

/-! Return the same one-sided H4 field from its genuine transmission chart.
The fixed extension is linear and bounded and agrees pointwise inside;
no zero trace, independent solution or boundary representative is introduced. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology Manifold
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.BoundaryTangential
open PoincareMT.LeviCivitaData.Dirichlet
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_transmission_chart_physical_extension {Ω V : Set E}
    (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hflat : ∀ x∈e.source,e x∈Ω ↔ 0<x 0)
    (hV : IsOpen V) (hVs : V⊆e.source)
    (a : E) (ha : a∈e.target) (haV : e.symm a∈V) :
    ∃ (N : Set E) (L : (E → ℝ) →ₗ[ℝ] (E → ℝ)) (C : ℝ≥0∞),
      a∈N ∧ IsOpen N ∧ IsCompact (closure N) ∧ closure N⊆e.target ∧ C≠⊤ ∧
      ∀ u : E → ℝ,MemWkp 4 2 (u∘e) (V∩halfSpace 3) →
        MemWkp 4 2 (L u) N ∧
        iteratedWeakSobolevNorm 4 2 (L u) N≤C*iteratedWeakSobolevNorm 4 2 (u∘e) (V∩halfSpace 3) ∧
        EqOn (L u) u (N∩Ω) := by
  obtain ⟨N,L,C,haN,hN,hNc,hNt,hC,hb⟩ := exists_chart_physical_linear_extension
    e he hei hflat (fun _ => 1) hV (fun _ _ => rfl) a ha haV
  refine ⟨N,L,C,haN,hN,hNc,hNt,hC,?_⟩
  intro u hu
  have heq : chartPullback e (fun y => (1:ℝ)*u y) =ᵐ[volume.restrict (V∩halfSpace 3)] u∘e := by
    filter_upwards [ae_restrict_mem (hV.inter isOpen_halfSpace).measurableSet] with x hx
    simp only [chartPullback_apply e _ (hVs hx.1),one_mul,Function.comp_def]
  have hh := hb u ((MemWkp_congr_ae (by norm_num) (hV.inter isOpen_halfSpace) heq).mpr hu)
  have heN := wkpNorm_congr_ae (k:=4) (by norm_num : (1:ℝ≥0∞)≤2) (hV.inter isOpen_halfSpace) heq
  exact ⟨hh.1,by simpa only [heN] using hh.2.1,hh.2.2⟩

#print axioms exists_transmission_chart_physical_extension
end Yamabe3.Analysis.UniformElliptic
