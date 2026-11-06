import Yamabe3.Analysis.UniformElliptic.NativeSmallGeometricError
import Yamabe3.Analysis.UniformElliptic.LocalUniformJet
import Yamabe3.Analysis.UniformElliptic.DivergenceScaling

/-!
# Small actual principal error on punctured neighborhoods

The same native rescaled error is local in the full germ of its input.
The compact extension needed by the global profile estimate is constructed
inside the proof. Thus the uniform small H4-to-H2 estimate applies to the
actual representative smooth only near the closure of an annular domain;
no smoothness through the removed pole is added.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ENNReal BigOperators

namespace Yamabe3.Analysis.UniformElliptic

open PoincareMT Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem nativeScaledGeometricError_eq_of_eventuallyEq
    (g : RiemannianMetric 3 E3) (r : ℝ) {u v : E3 → ℝ} {x : E3}
    (h : u =ᶠ[𝓝 x] v) :
    nativeScaledGeometricError g r u x = nativeScaledGeometricError g r v x := by
  have he := secondOrderOperator_eq_of_eventuallyEq
    (fun z i j => nativeScaledPrincipalError g r i j z)
    (nativeScaledFirstError g r) h
  simpa only [nativeScaledGeometricError, secondOrderPerturbation,
    secondOrderOperator, zero_mul, add_zero] using he

theorem nativeScaledGeometricError_eventuallyEq
    (g : RiemannianMetric 3 E3) (r : ℝ) {u v : E3 → ℝ} {x : E3}
    (h : u =ᶠ[𝓝 x] v) :
    nativeScaledGeometricError g r u =ᶠ[𝓝 x] nativeScaledGeometricError g r v := by
  filter_upwards [h.eventually_nhds] with y hy
  exact nativeScaledGeometricError_eq_of_eventuallyEq g r hy

theorem nativeScaledGeometricError_eq_negative_principalSource_locally
    (g : RiemannianMetric 3 E3) (r : ℝ) {O : Set E3} (hO : IsOpen O)
    {v : E3 → ℝ} (hv : ContDiffOn ℝ ∞ v O) {x : E3} (hx : x ∈ O) :
    nativeScaledGeometricError g r v x =
      -principalSource (fun z => nativeDivergenceMatrix g (r • z) - 1) v x := by
  obtain ⟨V, hV, _, hVv⟩ := exists_smooth_compact_extension_near_compact
    hO (isCompact_singleton (x := x)) (singleton_subset_iff.mpr hx) hv
  have hg := hVv x (mem_singleton x)
  rw [← nativeScaledGeometricError_eq_of_eventuallyEq g r hg,
    nativeScaledGeometricError_eq_negative_principalSource g r hV,
    principalSource_eq_of_eventuallyEq _ hg]

/-- The scale is uniform before the domain, its neighborhood, and the local
representative. The derivative profiles are those of the actual functions
on the very same domain. -/
theorem exists_uniform_local_small_native_geometric_error
    {ι : Type*} (Λ : Finset ι) (gE : ι → RiemannianMetric 3 E3)
    (hB : ∀ p ∈ Λ, (gE p).euclideanCoefficients 0 = innerSL ℝ)
    (hρ : ∀ p ∈ Λ, (gE p).pullbackVolumeDensity id 0 = 1)
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 ≤ r → r < δ → ∀ p ∈ Λ,
      ∀ (O Ω : Set E3), IsOpen O → IsOpen Ω → IsCompact (closure Ω) →
        closure Ω ⊆ O → Ω ⊆ closedBall (0 : E3) R →
        ∀ v : E3 → ℝ, ContDiffOn ℝ ∞ v O →
          derivativeProfile 2 Ω 2 (nativeScaledGeometricError (gE p) r v) ≤
            ENNReal.ofReal τ * derivativeProfile 2 Ω 4 v := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_uniform_small_native_geometric_error Λ gE hB hρ hR hτ
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ p hp O Ω hO hΩ hΩc hΩO hΩR v hv
  obtain ⟨V, hV, _, hVv⟩ := exists_smooth_compact_extension_near_compact hO hΩc hΩO hv
  have hvv (x : E3) (hx : x ∈ Ω) : V =ᶠ[𝓝 x] v := hVv x (subset_closure hx)
  have he := (hsmall r hr hrδ p hp).2.2 Ω hΩ hΩR V hV
  rw [derivativeProfile_eq_of_local_germs hΩ.measurableSet
      (fun x hx => nativeScaledGeometricError_eventuallyEq (gE p) r (hvv x hx)) 2 2,
    derivativeProfile_eq_of_local_germs hΩ.measurableSet hvv 2 4] at he
  exact he

#print axioms nativeScaledGeometricError_eq_of_eventuallyEq
#print axioms nativeScaledGeometricError_eventuallyEq
#print axioms nativeScaledGeometricError_eq_negative_principalSource_locally
#print axioms exists_uniform_local_small_native_geometric_error

end Yamabe3.Analysis.UniformElliptic
