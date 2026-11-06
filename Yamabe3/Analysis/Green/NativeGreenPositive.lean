import Yamabe3.Analysis.Green.NativeGreenNonnegative
import Yamabe3.Analysis.Green.NativeSchrodingerMaximum
import Yamabe3.Geometry.PuncturedConnected

/-! Strictly positive native Green existence for every pole. -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet
open Yamabe3.Parametrix

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
/-- Nonnegativity and the genuine pole-neighborhood positivity propagate
through the connected actual punctured manifold by the proved native
Schrodinger maximum principle. -/
theorem pos_of_native_green_nonneg (g : RiemannianMetric 3 M) (p : M) (G : M → ℝ)
    (hGs : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ G ({p}ᶜ))
    (hGP : ∀ x ∈ ({p}ᶜ : Set M), -g.leviCivitaData.laplacian G x +
      (g.leviCivitaData.scalarCurvature x / 8) * G x = 0)
    (hGn : ∀ x : M, x ≠ p → 0 ≤ G x)
    (hnear : ∃ O : Set M, IsOpen O ∧ p ∈ O ∧ ∀ x ∈ O, x ≠ p → 0 < G x) :
    ∀ x : M, x ≠ p → 0 < G x := by
  classical
  obtain ⟨O, hO, hpO, hnear⟩ := hnear
  have hΩ : IsOpen ({p}ᶜ : Set M) := isClosed_singleton.isOpen_compl
  have hconn : IsPreconnected ({p}ᶜ : Set M) := by
    simpa only [Finset.coe_singleton] using
      (Yamabe3.Geometry.isPathConnected_finset_compl ({p} : Finset M)).isConnected.isPreconnected
  have hdense : Dense ({p}ᶜ : Set M) :=
    Poincare.Topology.Manifold.dense_compl_countable (n := 1) (countable_singleton p)
  obtain ⟨q, hqO, hqp⟩ := hdense.inter_open_nonempty O hO ⟨p, hpO⟩
  have hqne : q ≠ p := by simpa only [mem_compl_iff, mem_singleton_iff] using hqp
  have hpositive : ∀ x ∈ ({p}ᶜ : Set M), 0 < G x :=
    g.leviCivitaData.pos_of_nonneg_schrodinger_on hΩ hconn
      (fun x => g.leviCivitaData.scalarCurvature x / 8)
      (g.leviCivitaData.continuous_scalarCurvature.div_const 8) hGs
      (fun x hx => hGn x (by simpa using hx))
      (fun x hx => by have h := hGP x hx; linarith)
      ⟨q, hqp, hnear q hqO hqne⟩
  exact fun x hx => hpositive x (by simpa using hx)

/-- The constructed native Green function is strictly positive at every
point different from its pole. The proof derives all Green construction,
regularity, sign and maximum-principle inputs from g, true Y>0 and p. -/
theorem exists_native_positive_green (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (p : M) :
    ∃ G : M → ℝ, MemLp G 2 g.volumeMeasure ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ G ({p}ᶜ) ∧
      (∀ x ∈ ({p}ᶜ : Set M), -g.leviCivitaData.laplacian G x +
        (g.leviCivitaData.scalarCurvature x / 8) * G x = 0) ∧
      (∀ φ : EnergyTest g.leviCivitaData univ,
        (∫ x, (-g.leviCivitaData.laplacian φ x +
          (g.leviCivitaData.scalarCurvature x / 8) * φ x) * G x
            ∂g.volumeMeasure) = 4 * Real.pi * φ p) ∧
      ∀ x : M, x ≠ p → 0 < G x := by
  obtain ⟨G, hGmem, hGs, hGP, hGt, hGn, hnear⟩ := exists_native_nonnegative_green g hY p
  exact ⟨G, hGmem, hGs, hGP, hGt, pos_of_native_green_nonneg g p G hGs hGP hGn hnear⟩

#print axioms pos_of_native_green_nonneg
#print axioms exists_native_positive_green

end Yamabe3.Analysis.GreenParametrix
