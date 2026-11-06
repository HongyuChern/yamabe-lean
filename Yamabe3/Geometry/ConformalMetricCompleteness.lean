import PoincareLib.Geometry.RicciFlow.Harnack.Basic
import Yamabe3.Geometry.BarrierCompleteness
import Mathlib.Geometry.Manifold.Algebra.Structures
import PoincareLib.Geometry.Riemannian.Distance.DerivativeLipschitz
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Construction.MetricCombination

/-!
# Native metric completeness under actual conformal lower bounds

These are the unchanged metric/barrier proofs extracted from Completeness.
Geodesic existence is retained in that original module. This separation
lets metric arguments compile without importing the geodesic-flow chain.
-/

set_option autoImplicit false
open scoped Manifold ContDiff



namespace Yamabe3.Geometry

open PoincareMT
open scoped Bundle

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The proper-barrier criterion for the actual path distance of a smooth
Riemannian metric. Establishing these two barrier properties is a separate
geometric proof obligation in a punctured Yamabe application. -/
theorem metricComplete_of_compact_barrier_sublevels
    (g : RiemannianMetric n M) (b : M → ℝ)
    (hcompact : ∀ R : ℝ, IsCompact {x : M | b x ≤ R})
    (hgrowth : ∀ x y : M, g.edist x y ≠ ⊤ →
      b x ≤ b y + (g.edist x y).toReal) :
    MetricComplete g := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  change CompleteSpace M
  exact Yamabe3.Topology.completeSpace_of_compact_barrier_sublevels b hcompact hgrowth

end Yamabe3.Geometry

namespace Yamabe3.Geometry

open PoincareMT

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Compact barrier sublevels and a pointwise tangent derivative bound imply
completeness. The derivative estimate is integrated along the actual paths
whose lengths define the metric, without assuming geodesic completeness. -/
theorem metricComplete_of_compact_sublevels_derivative_bound
    (g : RiemannianMetric n M) (b : M → ℝ)
    (hb : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 b)
    (hcompact : ∀ R : ℝ, IsCompact {x : M | b x ≤ R})
    (hgrad : ∀ x v, |mvfderiv (𝓡 n) b x v| ≤ g.tangentNorm x v) :
    MetricComplete g := by
  apply metricComplete_of_compact_barrier_sublevels g b hcompact
  intro x y hfinite
  have he := g.edist_le_mul_edist_of_derivative_bound hb
    (K := 1) (by norm_num) (by simpa using hgrad) x y
  have he' : EDist.edist (b x) (b y) ≤ g.edist x y := by
    simpa using he
  have hr : |b x - b y| ≤ (g.edist x y).toReal := by
    simpa [edist_dist, Real.dist_eq] using ENNReal.toReal_mono hfinite he'
  have hle : b x - b y ≤ (g.edist x y).toReal :=
    (le_abs_self (b x - b y)).trans hr
  linarith

/-- Under a fourth-power conformal change the actual tangent norm is
multiplied by the square of the positive conformal factor. -/
theorem tangentNorm_positiveScaling_fourth
    (g : RiemannianMetric n M) (u : M → ℝ)
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u) (hpos : ∀ x, 0 < u x)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    (MetricSurgery.positiveScaling g (fun y => u y ^ 4) (hu.pow 4)
      (fun y => pow_pos (hpos y) 4)).tangentNorm x v =
      u x ^ 2 * g.tangentNorm x v := by
  change Real.sqrt (u x ^ 4 * g.inner x v v) =
    u x ^ 2 * Real.sqrt (g.inner x v v)
  rw [show u x ^ 4 = (u x ^ 2) ^ 2 by ring,
    Real.sqrt_mul (sq_nonneg (u x ^ 2)), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (sq_nonneg (u x))]

/-- A concrete completeness criterion for a fourth-power conformal metric.
The barrier is a real function on the actual manifold; its compact sublevels
and the displayed base-metric derivative estimate must both be established. -/
theorem metricComplete_conformal_of_compact_sublevels_derivative_bound
    (g : RiemannianMetric n M) (u : M → ℝ)
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u) (hpos : ∀ x, 0 < u x)
    (b : M → ℝ) (hb : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 b)
    (hcompact : ∀ R : ℝ, IsCompact {x : M | b x ≤ R})
    (hgrad : ∀ x v, |mvfderiv (𝓡 n) b x v| ≤
      u x ^ 2 * g.tangentNorm x v) :
    MetricComplete (MetricSurgery.positiveScaling g (fun y => u y ^ 4)
      (hu.pow 4) (fun y => pow_pos (hpos y) 4)) := by
  apply metricComplete_of_compact_sublevels_derivative_bound _ b hb hcompact
  intro x v
  rw [tangentNorm_positiveScaling_fourth g u hu hpos x v]
  exact hgrad x v

end Yamabe3.Geometry


