import Yamabe3.Analysis.Green.NativeGreenConstruction
import Yamabe3.Analysis.GreenNonnegative

/-! Global nonnegativity of the constructed actual Green function. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet
open Yamabe3.Parametrix
open Yamabe3.Analysis.GreenPositivity

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

/-- Only actual geometry and the true positive Yamabe constant are inputs.
The constructed Green representative is nonnegative everywhere off its
pole and strictly positive on an actual punctured neighborhood of it. -/
theorem exists_native_nonnegative_green (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (p : M) :
    ∃ G : M → ℝ, MemLp G 2 g.volumeMeasure ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ G ({p}ᶜ) ∧
      (∀ x ∈ ({p}ᶜ : Set M), -g.leviCivitaData.laplacian G x +
        (g.leviCivitaData.scalarCurvature x / 8) * G x = 0) ∧
      (∀ φ : EnergyTest g.leviCivitaData univ,
        (∫ x, (-g.leviCivitaData.laplacian φ x +
          (g.leviCivitaData.scalarCurvature x / 8) * φ x) * G x
            ∂g.volumeMeasure) = 4 * Real.pi * φ p) ∧
      (∀ x : M, x ≠ p → 0 ≤ G x) ∧
      ∃ O : Set M, IsOpen O ∧ p ∈ O ∧ ∀ x ∈ O, x ≠ p → 0 < G x := by
  obtain ⟨G, hGmem, hGs, hGP, hGt, O, hO, hpO, hpos⟩ := exists_native_smooth_green g hY p
  have hnear : ∃ O : Set M, IsOpen O ∧ p ∈ O ∧ ∀ x ∈ O, x ≠ p → 0 ≤ G x :=
    ⟨O, hO, hpO, fun x hx hxp => (hpos x hx hxp).le⟩
  exact ⟨G, hGmem, hGs, hGP, hGt, nonneg_of_native_pointSource g hY p G hGs hnear hGt,
    O, hO, hpO, hpos⟩

#print axioms exists_native_nonnegative_green

end Yamabe3.Analysis.GreenParametrix
