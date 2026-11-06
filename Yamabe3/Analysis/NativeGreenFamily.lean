import Yamabe3.Analysis.GreenSymmetry
import Yamabe3.Analysis.Green.NativeGreenConstructionData

/-!
# A genuine symmetric positive native Green family

Each pole uses one set of witnesses from the proved native construction.
The highest theorem has only the original metric and its true positive
Yamabe constant as mathematical inputs. The coordinates, residuals, weak
inverse representatives, positivity and reciprocal identity are all proved
or chosen from that actual construction inside the proof.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet
open Yamabe3.Parametrix

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

/-- The actual positive symmetric Green family for the native operator
`P_g = -Delta_g + R_g/8`, normalized by `P_g G_p = 4*pi*delta_p`.
No Green, inverse, coordinate, regularity or positivity premise is an input.
The value on the diagonal is a harmless totalization, and all pointwise
PDE, positivity and reciprocity assertions explicitly exclude that diagonal. -/
theorem exists_native_positive_symmetric_green_family (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) :
    ∃ G : M → M → ℝ,
      (∀ p : M, MemLp (G p) 2 g.volumeMeasure) ∧
      (∀ p : M, ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (G p) ({p}ᶜ)) ∧
      (∀ p x : M, x ≠ p →
        -g.leviCivitaData.laplacian (G p) x +
          (g.leviCivitaData.scalarCurvature x / 8) * G p x = 0) ∧
      (∀ p : M, ∀ φ : EnergyTest g.leviCivitaData univ,
        (∫ x, (-g.leviCivitaData.laplacian φ x +
          (g.leviCivitaData.scalarCurvature x / 8) * φ x) * G p x
            ∂g.volumeMeasure) = 4 * Real.pi * φ p) ∧
      (∀ p x : M, x ≠ p → 0 < G p x) ∧
      ∀ p q : M, p ≠ q → G p q = G q p := by
  classical
  choose e r gE χ F hF U hr hrs hep he hei hχr hχsource hB0 hΓ0 hcoeff hGauss
    hρ0 hzero hFformula hUc hUae hGmem hGs hGP hGt hpositive using
      fun p : M => exists_native_green_construction_data g hY p
  let G : M → M → ℝ := fun p x => singular (e p) (χ p) x - U p x
  refine ⟨G, hGmem, hGs, ?_, hGt, hpositive, ?_⟩
  · intro p x hxp
    exact hGP p x (by simpa using hxp)
  · intro p q hpq
    have hχball (s : M) : tsupport (χ s) ⊆ ball (0 : E) (r s) := by
      rw [(χ s).tsupport_eq]
      exact closedBall_subset_ball (hχr s)
    have hFactual (s : M) :
        MemLp (coordinateExtension (e s) (nativeResidual (gE s) (χ s))) 2 g.volumeMeasure := by
      rw [← hFformula s]
      exact hF s
    have hUactual (s : M) : U s =ᵐ[g.volumeMeasure]
        (toL2 g.leviCivitaData univ
          (closedConformalLaplacianL2Solution g hY
            ((hFactual s).toLp
              (coordinateExtension (e s) (nativeResidual (gE s) (χ s)))) ) : M → ℝ) := by
      simpa only [hFformula s] using hUae s
    have hsource : ∀ φ : EnergyTest g.leviCivitaData univ,
        (∫ x, (-g.leviCivitaData.laplacian φ x +
          (g.leviCivitaData.scalarCurvature x / 8) * φ x) *
            (singular (e p) (χ p) x - U p x) ∂g.volumeMeasure) =
              4 * Real.pi * φ (e p 0) := by
      simpa only [hep p] using hGt p
    have hsym := native_green_symmetry_of_construction g hY (gE p) (gE q) (e p) (e q)
      (he p) (hei p) (he q) (hei q) isOpen_ball (ball_subset_closedBall.trans (hrs p))
      isOpen_ball (ball_subset_closedBall.trans (hrs q))
      (fun x hx => hcoeff p x (ball_subset_closedBall hx))
      (fun x hx => hcoeff q x (ball_subset_closedBall hx))
      (hGauss p) (hGauss q) (hρ0 p) (hρ0 q) (hzero p) (hzero q)
      (χ p) (χ q) (hχball p) (hχball q) (hFactual p) (hFactual q)
      (U p) (U q) (hUc p) (hUc q) (hUactual p) (hUactual q) hsource
      (by simpa only [hep p, hep q] using hpq)
    simpa only [hep p, hep q] using hsym

#print axioms exists_native_positive_symmetric_green_family

end Yamabe3.Analysis.GreenParametrix
