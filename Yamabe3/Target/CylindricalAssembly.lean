import Yamabe3.Target.Statement
import Yamabe3.Geometry.FiniteCylindricalCompleteness

/-! The final target from the same positive smooth PDE solution and its
physical lower bounds at the prescribed ends. -/

set_option autoImplicit false
open Metric
open scoped Manifold ContDiff
open PoincareMT Yamabe3.Parametrix

namespace Yamabe3.Target

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

/-- A positive smooth solution with the cylindrical lower bound at every
prescribed point yields the full geometric conclusion for that same solution. -/
theorem puncturedConclusion_of_cylindrical_solution
    (g : RiemannianMetric 3 M) (Λ : Finset M) (hΛ : Λ.Nonempty)
    (u : M → ℝ)
    (hu : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ u (Λ : Set M)ᶜ)
    (hpos : ∀ y ∉ Λ, 0 < u y)
    (heq : let O := puncturedOpen Λ
      let D := (Geometry.restrictMetric g O).leviCivitaData
      let U : O → ℝ := fun y => u y.val
      ∀ x, -8 * D.laplacian U x + D.scalarCurvature x * U x = 6 * U x ^ 5)
    (e : M → OpenPartialHomeomorph E M) (χ : M → ContDiffBump (0 : E))
    (h0 : ∀ p ∈ Λ, (0 : E) ∈ (e p).source)
    (hep : ∀ p ∈ Λ, e p 0 = p)
    (he : ∀ p ∈ Λ, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e p) (e p).source)
    (hei : ∀ p ∈ Λ, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e p).symm (e p).target)
    (hχ : ∀ p ∈ Λ, tsupport (χ p) ⊆ (e p).source)
    (ρ : M → ℝ) (hρ : ∀ p ∈ Λ, 0 < ρ p)
    (hGauss : ∀ p ∈ Λ, ∀ x ∈ ball (0 : E) (ρ p), ∀ w : E,
      g.pullbackCoefficients (e p) x x w = inner ℝ x w)
    (c r : M → ℝ) (hc : ∀ p ∈ Λ, 0 < c p) (hr : ∀ p ∈ Λ, 0 < r p)
    (hlower : ∀ p ∈ Λ, ∀ x : E, e p x ∉ Λ → 0 < ‖x‖ → ‖x‖ < r p →
      c p * ‖x‖⁻¹ ≤ u (e p x) ^ 2) :
    puncturedConclusion g Λ := by
  obtain ⟨hU, hpositive, hcomplete, hfinite, hgeodesic⟩ :=
    Geometry.CylindricalCompleteness.native_complete_finite_cylindrical_ends
      g Λ hΛ u hu hpos e χ h0 hep he hei hχ ρ hρ hGauss c r hc hr hlower
  exact ⟨fun y => u y.val, hU, hpositive, heq, hcomplete, hfinite, hgeodesic⟩

end Yamabe3.Target
