import Yamabe3.Geometry.OpenRestriction
import Yamabe3.Geometry.ConformalYamabe
import PoincareLib.Geometry.Riemannian.Connection.Construction
import PoincareLib.Geometry.Riemannian.Measure.Basic
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Construction.MetricCombination
import PoincareLib.Geometry.Riemannian.Geodesic.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The independent target proposition

This file DEFINES the full target; it does not prove it. No existence theorem,
weighted inverse, mass theorem, or completeness assertion is an input field.
The Yamabe constant uses the genuine energy quotient, not coercivity renamed.
The metric, Laplacian, scalar curvature and distance are native geometric data.
The quotient-definition agreement with alternate conventions is a separate
interface to check before using an externally formalized Yamabe theorem.
-/

set_option autoImplicit false

open MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Bundle

noncomputable section

namespace Yamabe3.Target

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- The three-dimensional Yamabe numerator, with coefficient 8. -/
def energy (g : PoincareMT.RiemannianMetric 3 M) (v : M → ℝ) : ℝ :=
  let D := g.leviCivitaData
  ∫ x, (8 * g.inner x (D.gradient v x) (D.gradient v x) +
    D.scalarCurvature x * v x ^ 2) ∂g.volumeMeasure

/-- The genuine critical quotient; its denominator is the squared L6 norm. -/
def quotient (g : PoincareMT.RiemannianMetric 3 M) (v : M → ℝ) : ℝ :=
  energy g v / (∫ x, |v x| ^ 6 ∂g.volumeMeasure) ^ (1 / 3 : ℝ)

/-- Infimum over nonzero smooth real test functions. On the closed connected
manifolds of the target, the denominator is positive for each such function.
That nonvanishing and the coercivity consequences still require proofs. -/
def yamabeConstant (g : PoincareMT.RiemannianMetric 3 M) : ℝ :=
  sInf {q : ℝ | ∃ v : M → ℝ,
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ v ∧ v ≠ 0 ∧ q = quotient g v}

/-- The inherited smooth open manifold M minus the specified finite set. -/
def puncturedOpen (Λ : Finset M) : Opens M :=
  ⟨(Λ : Set M)ᶜ, Λ.finite_toSet.isClosed.isOpen_compl⟩

/-- Both actual metric completeness and the full all-initial-data smooth
geodesic conclusion are retained explicitly. -/
def puncturedConclusion (g : PoincareMT.RiemannianMetric 3 M) (Λ : Finset M) : Prop :=
  let O := puncturedOpen Λ
  let gO := Geometry.restrictMetric g O
  let D := gO.leviCivitaData
  ∃ (u : O → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u) (hpos : ∀ x, 0 < u x),
    (∀ x, -8 * D.laplacian u x + D.scalarCurvature x * u x = 6 * u x ^ 5) ∧
    let ghat := PoincareMT.MetricSurgery.positiveScaling gO (fun x => u x ^ 4)
      (hu.pow 4) (fun x => pow_pos (hpos x) 4)
    PoincareMT.MetricComplete ghat ∧
      (∀ x y : O, ghat.edist x y ≠ ⊤) ∧
      ∀ (x : O) (v : EuclideanSpace ℝ (Fin 3)), ∃ γ : ℝ → O,
        ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ γ ∧
        ghat.IsGeodesicOn γ Set.univ ∧ γ 0 = x ∧
        HasDerivAt (fun t => extChartAt (𝓡 3) x (γ t)) v 0

/-- CANDIDATE FINAL STATEMENT, not a theorem with a proof. Compactness and
connectedness express the closed connected background in the target.
No orientability, local flatness, or nondegeneracy assumptions occur. -/
def generalThreeDimensionalPuncturedYamabe
    [CompactSpace M] [ConnectedSpace M] : Prop :=
  ∀ (g : PoincareMT.RiemannianMetric 3 M) (Λ : Finset M),
    0 < yamabeConstant g → 2 ≤ Λ.card → puncturedConclusion g Λ

end Yamabe3.Target
