import PoincareLib.Geometry.Riemannian.Geodesic.Complete
import Yamabe3.Geometry.ConformalMetricCompleteness

/-!
# Metric completeness and smooth complete geodesics

This module uses the native intrinsic metric-completeness predicate and the
native affine geodesic equation from the fixed PoincareLib dependency. It does
not assert that a singular Yamabe solution or its completeness has been proved.

Upstream interfaces: PoincareLib commit
`62db01af9388dc1d9b56b66d6674f4c09b2318a2`,
`Geometry/Riemannian/Geodesic/Complete.lean`.
No upstream implementation has been copied.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

namespace Yamabe3.Geometry

open PoincareMT

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Every initial position and coordinate velocity for a complete smooth
Riemannian metric have a smooth geodesic defined for all real times. -/
theorem exists_smooth_global_geodesic (g : RiemannianMetric n M)
    (hc : MetricComplete g) (p : M) (v : EuclideanSpace ℝ (Fin n)) :
    ∃ γ : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ ∧
      g.IsGeodesicOn γ Set.univ ∧ γ 0 = p ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0 := by
  obtain ⟨γ, hγ, hγ0, hv⟩ := g.exists_global_geodesic hc p v
  exact ⟨γ, RiemannianMetric.contMDiff_global_geodesic hγ, hγ, hγ0, hv⟩

end Yamabe3.Geometry

