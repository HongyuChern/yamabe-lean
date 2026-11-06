import Yamabe3.Analysis.NativeCompletedChartScaling
import Yamabe3.Analysis.NativeChartAeTransport

/-! The actual completed dilation/chart map retains any proved full
volume representative of the same Euclidean element. The desired
representative is not independently assumed to be an L2 function. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem nativeCompletedChartL2_same_function
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    {a:ℝ} (ha:0 < a) (ha1:a ≤ 1) {O:Set E} (z:H1Zero Deuc O) (u:E→ℝ)
    (hz:(toL2 Deuc O z:E→ℝ)=ᵐ[volume]u) :
    (nativeCompactChartL2CLM g e he hei hK hKs (euclideanL2DilationCLM ha ha1 (toL2 Deuc O z)):M→ℝ)
      =ᵐ[g.volumeMeasure]nativeCompactChartFunction e K (fun x:E=>u (a⁻¹ • x)) := by
  have hd:(euclideanL2DilationCLM ha ha1 (toL2 Deuc O z):E→ℝ)=ᵐ[volume]
      fun x:E=>toL2 Deuc O z (a⁻¹ • x) := by
    simpa only [native_euclideanMetric_volumeMeasure] using euclideanL2DilationCLM_ae ha ha1 (toL2 Deuc O z)
  have hu:(fun x:E=>toL2 Deuc O z (a⁻¹ • x))=ᵐ[volume]fun x:E=>u (a⁻¹ • x) := by
    simpa only [preimage_univ,Measure.restrict_univ] using
      ae_comp_dilation (inv_ne_zero ha.ne') (ae_restrict_of_ae (s:=univ) hz)
  have hc:=nativeCompactChart_congr_volume_ae g e he hei hK.measurableSet
    (ae_restrict_of_ae (s:=K) (hd.trans hu))
  exact (nativeCompactChartL2Linear_ae g e he hei hK hKs (euclideanL2DilationCLM ha ha1 (toL2 Deuc O z))).trans hc

#print axioms nativeCompletedChartL2_same_function
end Yamabe3.Analysis.SpherePolar
