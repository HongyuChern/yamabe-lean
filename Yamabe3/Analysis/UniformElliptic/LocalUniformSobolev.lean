import Yamabe3.Analysis.UniformElliptic.LocalUniformJet

/-!
# The uniform gain of two derivatives for actual local representatives

The solution, source and signed potential need only be smooth on an open
neighborhood of the integration region. Genuine compact extensions retain
their germs, the weak equation and all derivative profiles. In particular
k = 2 gives H2 source to H4 solution, without the extra source derivatives
used by the older direct pointwise jet estimate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- One constant, chosen before all coefficients and functions, controls
the same local solution with a gain of exactly two Sobolev derivatives.
No global smoothness across an excluded pole is imposed. -/
theorem exists_local_uniform_derivativeProfile_add_two_with_potential
    (k : ℕ) {Ω O V W : Set E} (hO : IsOpen O)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    (hVΩ : closure V ⊆ Ω) (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hWV : closure W ⊆ V) {κ L Q : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : SmoothEllipticBilinearForm d Ω), κ ≤ B.lam →
      (∀ n ≤ k + 2, ∀ x ∈ V, ∀ i j : Fin d,
        ‖iteratedFDeriv ℝ n (fun y => B.a y i j) x‖ ≤ L) →
      (∀ x ∈ V, (∑ i : Fin d, ∑ j : Fin d,
        (B.a x i j - (1 : Matrix (Fin d) (Fin d) ℝ) i j) ^ 2) ≤ 1 / 4) →
      ∀ (q : E → ℝ), ContDiffOn ℝ ∞ q O →
      (∀ n ≤ k, ∀ x ∈ V, ‖iteratedFDeriv ℝ n q x‖ ≤ Q) →
      ∀ {u f : E → ℝ}, ContDiffOn ℝ ∞ u O → ContDiffOn ℝ ∞ f O →
        WeakEquation V (matrixFlux B.a (fun j => partialDeriv j u))
          (fun x => f x + q x * u x) →
        derivativeProfile 2 W (k + 2) u ≤ ENNReal.ofReal C *
          (derivativeProfile 2 V 0 u + derivativeProfile 2 V k f) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_derivativeProfile_add_two_with_potential
    k hV hVc hVΩ hW hWc hWV hκ hL hQ
  refine ⟨C, hC, ?_⟩
  intro B hB hjet hosc q hq hqjet u f hu hf heq
  obtain ⟨v, hv, _, hvu⟩ :=
    exists_smooth_compact_extension_near_compact hO hVc hVO hu
  obtain ⟨F, hF, _, hFf⟩ :=
    exists_smooth_compact_extension_near_compact hO hVc hVO hf
  obtain ⟨q₀, hq₀, _, hq₀q⟩ :=
    exists_smooth_compact_extension_near_compact hO hVc hVO hq
  have hvg (y : E) (hy : y ∈ V) : v =ᶠ[𝓝 y] u := hvu y (subset_closure hy)
  have hFg (y : E) (hy : y ∈ V) : F =ᶠ[𝓝 y] f := hFf y (subset_closure hy)
  have hqg (y : E) (hy : y ∈ V) : q₀ =ᶠ[𝓝 y] q := hq₀q y (subset_closure hy)
  have hq₀jet : ∀ n ≤ k, ∀ x ∈ V, ‖iteratedFDeriv ℝ n q₀ x‖ ≤ Q := by
    intro n hn x hx
    rw [((hqg x hx).iteratedFDeriv ℝ n).self_of_nhds]
    exact hqjet n hn x hx
  have heq' : WeakEquation V (matrixFlux B.a (fun j => partialDeriv j v))
      (fun y => F y + q₀ y * v y) := by
    intro φ hφ hφc hφV
    calc
      (∫ y in V, ∑ i, matrixFlux B.a (fun j => partialDeriv j v) i y *
          partialDeriv i φ y) =
          ∫ y in V, ∑ i, matrixFlux B.a (fun j => partialDeriv j u) i y *
            partialDeriv i φ y := by
        apply setIntegral_congr_fun hV.measurableSet
        intro y hy
        have hd (j : Fin d) : partialDeriv j v y = partialDeriv j u y :=
          congrArg (fun A : E →L[ℝ] ℝ => A (EuclideanSpace.single j 1)) (hvg y hy).fderiv_eq
        simp only [matrixFlux, hd]
      _ = ∫ y in V, (f y + q y * u y) * φ y := heq φ hφ hφc hφV
      _ = ∫ y in V, (F y + q₀ y * v y) * φ y := by
        apply setIntegral_congr_fun hV.measurableSet
        intro y hy
        change (f y + q y * u y) * φ y = (F y + q₀ y * v y) * φ y
        rw [(hvg y hy).self_of_nhds, (hFg y hy).self_of_nhds,
          (hqg y hy).self_of_nhds]
  have h := hbound B hB hjet hosc q₀ hq₀ hq₀jet hv hF heq'
  rw [derivativeProfile_eq_of_local_germs hV.measurableSet hvg 2 0,
    derivativeProfile_eq_of_local_germs hV.measurableSet hFg 2 k,
    derivativeProfile_eq_of_local_germs hW.measurableSet
      (fun x hx => hvg x (hWV (subset_closure hx))) 2 (k + 2)] at h
  exact h

#print axioms exists_local_uniform_derivativeProfile_add_two_with_potential

end Yamabe3.Analysis.UniformElliptic
