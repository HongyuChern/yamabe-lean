import Yamabe3.Analysis.Green.NativeGreenWeak
import Yamabe3.Analysis.NativeGreenFamily

/-!
# The actual positive symmetric Green family against all smooth tests

The same native-volume L2 Green family is smooth and strictly positive away
from its pole, is symmetric, and satisfies both operator normalizations
against every smooth scalar function on the actual closed manifold.
Compactness makes every such function a genuine compactly supported energy
test. No Dirac source is submitted to the H1 inverse.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff
noncomputable section
namespace Yamabe3.Analysis.GreenParametrix
open PoincareMT PoincareMT.LeviCivitaData.Dirichlet
variable {M : Type*} [TopologicalSpace M] [T3Space M]
 [MeasurableSpace M] [BorelSpace M]
 [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
 [CompactSpace M] [ConnectedSpace M]

/-- On the actual compact manifold, every smooth scalar function is an energy test. -/
theorem every_smooth_function_is_an_energy_test (g : RiemannianMetric 3 M)
    (φ : M → ℝ) (hφ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ φ) :
    ∃ ψ : EnergyTest g.leviCivitaData univ, (ψ : M → ℝ) = φ := by
  exact ⟨⟨φ, hφ, HasCompactSupport.of_compactSpace _, subset_univ _⟩, rfl⟩

/-- The same actually constructed family satisfies both normalization conventions
against every smooth test, and is strictly positive and symmetric off the diagonal. -/
theorem full_smooth_test_green_family (g : RiemannianMetric 3 M)
    (hY : 0 < Yamabe3.Target.yamabeConstant g) :
    ∃ G : M → M → ℝ,
      (∀ p, MemLp (G p) 2 g.volumeMeasure) ∧
      (∀ p, ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (G p) ({p}ᶜ)) ∧
      (∀ p x, x ≠ p → 0 < G p x) ∧
      (∀ p q, p ≠ q → G p q = G q p) ∧
      ∀ p (φ : M → ℝ), ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ φ →
        (∫ x, (-g.leviCivitaData.laplacian φ x +
          g.leviCivitaData.scalarCurvature x / 8 * φ x) * G p x
          ∂g.volumeMeasure) = 4 * Real.pi * φ p ∧
        (∫ x, (-8 * g.leviCivitaData.laplacian φ x +
          g.leviCivitaData.scalarCurvature x * φ x) * G p x
          ∂g.volumeMeasure) = 32 * Real.pi * φ p := by
  obtain ⟨G, hmem, hs, _, ht, hpos, hsym⟩ :=
    Yamabe3.Analysis.GreenParametrix.exists_native_positive_symmetric_green_family g hY
  refine ⟨G, hmem, hs, hpos, hsym, ?_⟩
  intro p φ hφ
  let ψ : EnergyTest g.leviCivitaData univ :=
    ⟨φ, hφ, HasCompactSupport.of_compactSpace _, subset_univ _⟩
  have h := ht p ψ
  change (∫ x, (-g.leviCivitaData.laplacian φ x +
    g.leviCivitaData.scalarCurvature x / 8 * φ x) * G p x ∂g.volumeMeasure) =
      4 * Real.pi * φ p at h
  refine ⟨h, ?_⟩
  calc
    _ = ∫ x, 8 * ((-g.leviCivitaData.laplacian φ x +
      g.leviCivitaData.scalarCurvature x / 8 * φ x) * G p x) ∂g.volumeMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring
    _ = 8 * (4 * Real.pi * φ p) := by rw [integral_const_mul, h]
    _ = _ := by ring

end Yamabe3.Analysis.GreenParametrix
