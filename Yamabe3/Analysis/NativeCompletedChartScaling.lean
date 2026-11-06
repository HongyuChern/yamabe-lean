import Yamabe3.Analysis.EuclideanCompletedDilation
import Yamabe3.Analysis.NativeWeakChartTransport
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Inclusion

/-! The same completed Euclidean field, first physically dilated and
then extended through the actual native chart. Its full native L2
operator and sqrt(a) norm cost are retained. This transports H1, not
the PDE; the operator residual must be proved separately. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
private def completedChartScaleNormed (g:RiemannianMetric 3 M) (O:Set M):
    NormedSpace ℝ (H1Zero g.leviCivitaData O):=inferInstance
attribute [local instance] completedChartScaleNormed
variable (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
  (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
  (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
  {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
  {a:ℝ} (ha:0 < a) (ha1:a ≤ 1) (O:Set E) (hfit:euclideanDilatedDomain a O⊆K)

def nativeEuclideanCompletedChartScaleCLM : H1Zero Deuc O →L[ℝ] H1Zero g.leviCivitaData univ :=
  (inclusion (D:=g.leviCivitaData) (subset_univ (e '' euclideanDilatedDomain a O))).comp
    ((nativeWeakChartH1CLM g e he hei hK hKs hfit).comp (euclideanH1DilationCLM ha ha1 O))

theorem nativeEuclideanCompletedChartScaleCLM_norm :
    ‖nativeEuclideanCompletedChartScaleCLM g e he hei hK hKs ha ha1 O hfit‖ ≤
      nativeWeakChartBound g e he hei hK hKs*Real.sqrt a := by
  have hC:=nativeWeakChartBound_pos g e he hei hK hKs
  apply (nativeEuclideanCompletedChartScaleCLM g e he hei hK hKs ha ha1 O hfit).opNorm_le_bound (by positivity)
  intro z
  change ‖inclusion (D:=g.leviCivitaData) _
    (nativeWeakChartH1CLM g e he hei hK hKs hfit (euclideanH1DilationCLM ha ha1 O z))‖ ≤ _
  rw [norm_inclusion]
  exact ((nativeWeakChartH1CLM_norm_le g e he hei hK hKs hfit _).trans
    (mul_le_mul_of_nonneg_left (euclideanH1DilationCLM_norm_le ha ha1 O z) hC.le)).trans_eq (by ring)

theorem nativeEuclideanCompletedChartScaleCLM_toL2 (z:H1Zero Deuc O) :
    toL2 g.leviCivitaData univ (nativeEuclideanCompletedChartScaleCLM g e he hei hK hKs ha ha1 O hfit z)=
      nativeCompactChartL2CLM g e he hei hK hKs (euclideanL2DilationCLM ha ha1 (toL2 Deuc O z)) := by
  simp only [nativeEuclideanCompletedChartScaleCLM,ContinuousLinearMap.comp_apply,toL2_inclusion,
    toL2_nativeWeakChartH1CLM,euclideanH1DilationCLM_toL2]

#print axioms nativeEuclideanCompletedChartScaleCLM_norm
#print axioms nativeEuclideanCompletedChartScaleCLM_toL2
end Yamabe3.Analysis.SpherePolar
