import Yamabe3.Analysis.NativeWeakChartDivergence

/-! The actual metric density ratio is a bounded Sobolev multiplier on a
fixed compact chart. The source remains the original physical function. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology Manifold
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_native_chart_density_ratio_source_bound (k : ℕ)
    (g : RiemannianMetric 3 E) (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O W : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOs : closure O⊆e.source) (hW : IsOpen W) (heW : e '' closure O⊆W) :
    ∃ C : ℝ≥0∞,C≠⊤ ∧ ∀ f : E → ℝ,MemWkp k 2 f W →
      MemWkp k 2 (fun x => nativeChartDensityRatio g e x*f (e x)) O ∧
      iteratedWeakSobolevNorm k 2 (fun x => nativeChartDensityRatio g e x*f (e x)) O ≤
        C*iteratedWeakSobolevNorm k 2 f W := by
  obtain ⟨P,hP,hp⟩ := exists_euclidean_chart_source_bound k e he hei hO hOc hOs hW heW
  obtain ⟨M,hM,hm⟩ := exists_local_sobolev_multiplier_bound k hO hOc e.open_source hOs
    (nativeChartDensityRatio g e) (nativeChartDensityRatio_smoothOn g e he hei)
  refine ⟨M*P,by finiteness,?_⟩
  intro f hf
  have hh := hm _ (hp f hf).1
  exact ⟨hh.1,hh.2.trans (by simpa only [mul_assoc] using (mul_le_mul (le_refl M) (hp f hf).2 zero_le zero_le))⟩

#print axioms exists_native_chart_density_ratio_source_bound
end Yamabe3.Analysis.UniformElliptic
