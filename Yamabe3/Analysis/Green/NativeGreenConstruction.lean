import Yamabe3.Analysis.Green.NativeManifoldParametrix
import Yamabe3.Analysis.GreenSmooth
import Yamabe3.Analysis.NativeGreenGrowth

/-!
# Native smooth Green construction with a continuous correction

All parametrix, weak-solution and regularity inputs are discharged here.
The conclusions use the actual native metric, volume, scalar curvature and
Laplacian. Positivity near the pole is proved from the constructed inverse
radius singularity and continuity of its correction. Global positivity,
symmetry and the nonlinear singular Yamabe equation remain separate nodes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set MeasureTheory Metric
open scoped Manifold ContDiff

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet
open Yamabe3.Parametrix

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

/-- The actual Green representative is the constructed native cutoff
Newton singularity minus an actual continuous function on the original
closed manifold. All regularity and testing assertions are proved. -/
theorem exists_native_green_with_continuous_correction (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (p : M) :
    ∃ (e : OpenPartialHomeomorph E M) (χ : ContDiffBump (0 : E)) (U : M → ℝ),
      e 0 = p ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      tsupport χ ⊆ e.source ∧ Continuous U ∧
      MemLp (fun x => singular e χ x - U x) 2 g.volumeMeasure ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x => singular e χ x - U x) ({p}ᶜ) ∧
      (∀ x ∈ ({p}ᶜ : Set M),
        -g.leviCivitaData.laplacian (fun y => singular e χ y - U y) x +
          (g.leviCivitaData.scalarCurvature x / 8) * (singular e χ x - U x) = 0) ∧
      ∀ φ : EnergyTest g.leviCivitaData univ,
        (∫ x, (-g.leviCivitaData.laplacian φ x +
          (g.leviCivitaData.scalarCurvature x / 8) * φ x) * (singular e χ x - U x)
            ∂g.volumeMeasure) = 4 * Real.pi * φ p := by
  obtain ⟨e, χ, F, hep, he, hei, hχ, hΦ, hF, hparam⟩ :=
    exists_native_pointSource_parametrix g p
  have hΦs : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (singular e χ) ({p}ᶜ) := by
    simpa only [hep] using contMDiffOn_singular e hei χ hχ
  obtain ⟨U, hUc, _, hGL2, hGs, hGP, hGt⟩ :=
    parametrix_correction_exists_smooth g hY p (singular e χ) F hΦ hF hΦs hparam
  exact ⟨e, χ, U, hep, he, hei, hχ, hUc, hGL2, hGs, hGP, hGt⟩

/-- A smooth native Green function exists away from every specified pole
and is strictly positive on an actual punctured neighborhood of that pole.
This theorem does not assert its as-yet separate global positivity. -/
theorem exists_native_smooth_green (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (p : M) :
    ∃ G : M → ℝ, MemLp G 2 g.volumeMeasure ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ G ({p}ᶜ) ∧
      (∀ x ∈ ({p}ᶜ : Set M), -g.leviCivitaData.laplacian G x +
        (g.leviCivitaData.scalarCurvature x / 8) * G x = 0) ∧
      (∀ φ : EnergyTest g.leviCivitaData univ,
        (∫ x, (-g.leviCivitaData.laplacian φ x +
          (g.leviCivitaData.scalarCurvature x / 8) * φ x) * G x
            ∂g.volumeMeasure) = 4 * Real.pi * φ p) ∧
      ∃ O : Set M, IsOpen O ∧ p ∈ O ∧ ∀ x ∈ O, x ≠ p → 0 < G x := by
  obtain ⟨e, χ, U, hep, _, _, hχ, hUc, hGL2, hGs, hGP, hGt⟩ :=
    exists_native_green_with_continuous_correction g hY p
  refine ⟨fun x => singular e χ x - U x, hGL2, hGs, hGP, hGt, ?_⟩
  simpa only [hep] using
    singular_sub_continuous_pos_on_punctured_neighborhood e χ hχ hUc.continuousAt

/-- The quantitative inverse-radius lower bound follows from the actual
constructed continuous correction, not an assumed Green asymptotic. -/
theorem exists_native_green_with_pole_lower_bound (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (p : M) :
    ∃ (e : OpenPartialHomeomorph E M) (χ : ContDiffBump (0 : E)) (U : M → ℝ),
      e 0 = p ∧ tsupport χ ⊆ e.source ∧ Continuous U ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x => singular e χ x - U x) ({p}ᶜ) ∧
      (∀ φ : EnergyTest g.leviCivitaData univ,
        (∫ x, (-g.leviCivitaData.laplacian φ x +
          (g.leviCivitaData.scalarCurvature x / 8) * φ x) * (singular e χ x - U x)
            ∂g.volumeMeasure) = 4 * Real.pi * φ p) ∧
      ∃ r : ℝ, 0 < r ∧ r ≤ χ.rIn ∧ ∀ x : E, 0 < ‖x‖ → ‖x‖ < r →
        (2 * ‖x‖)⁻¹ ≤ singular e χ (e x) - U (e x) := by
  obtain ⟨e, χ, U, hep, _, _, hχ, hUc, _, hGs, _, hGt⟩ :=
    exists_native_green_with_continuous_correction g hY p
  exact ⟨e, χ, U, hep, hχ, hUc, hGs, hGt,
    singular_sub_continuous_lower_bound e χ hχ hUc.continuousAt⟩

#print axioms exists_native_green_with_continuous_correction
#print axioms exists_native_smooth_green
#print axioms exists_native_green_with_pole_lower_bound

end Yamabe3.Analysis.GreenParametrix
