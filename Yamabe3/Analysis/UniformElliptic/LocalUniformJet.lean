import Yamabe3.Analysis.UniformElliptic.UniformJetEstimate

/-!
# Local smoothness suffices for the uniform jet estimate

The globally smooth test-function prerequisite is constructed, not assumed.
A genuine compactly supported cutoff extends every locally smooth function
without changing its germ anywhere on the prescribed compact set. Actual
weak equations, Sobolev profiles and all jets transfer through these germs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- An actual cutoff produces a globally smooth compact extension agreeing
with the original function on a neighborhood of every point of K. -/
theorem exists_smooth_compact_extension_near_compact
    {O K : Set E} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u O) :
    ∃ v : E → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
      ∀ x ∈ K, v =ᶠ[𝓝 x] u := by
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  obtain ⟨η, hη, hηc, _, hηone, hηO⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff (hK.cthickening (r := δ)) hO hδO
  refine ⟨fun x => η x * u x, ?_, hηc.mul_right, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ O
    · exact hη.contDiffAt.mul (hu.contDiffAt (hO.mem_nhds hx))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have hz := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hηO h))
      filter_upwards [hz] with y hy
      simp [hy]
  · intro x hx
    filter_upwards [isOpen_thickening.mem_nhds (self_subset_thickening hδ K hx)] with y hy
    rw [hηone y (thickening_subset_cthickening δ K hy), one_mul]

/-- Genuine derivative profiles are unchanged by equality of local germs
at all points in the integration set. -/
theorem derivativeProfile_eq_of_local_germs {V : Set E} (hV : MeasurableSet V)
    {u v : E → ℝ} (h : ∀ x ∈ V, u =ᶠ[𝓝 x] v) (p : ℝ≥0∞) (k : ℕ) :
    derivativeProfile p V k u = derivativeProfile p V k v := by
  unfold derivativeProfile
  apply Finset.sum_congr rfl
  intro n _
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hV] with x hx
  exact congrArg norm ((h x hx).iteratedFDeriv ℝ n).self_of_nhds

/-- Uniform pointwise regularity for functions smooth only on a genuine
open neighborhood. The globally smooth extensions required by the energy
estimate are built inside the proof and retain the original weak equation. -/
theorem exists_local_uniform_pointwise_jet_bound [NeZero d]
    (m : ℕ) {Ω O V K : Set E} (hO : IsOpen O)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    (hVΩ : closure V ⊆ Ω) (hK : IsCompact K) (hKV : K ⊆ V)
    {κ L Q : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : SmoothEllipticBilinearForm d Ω), κ ≤ B.lam →
      (∀ n ≤ m + 1 + d, ∀ x ∈ V, ∀ i j : Fin d,
        ‖iteratedFDeriv ℝ n (fun y => B.a y i j) x‖ ≤ L) →
      (∀ x ∈ V, (∑ i : Fin d, ∑ j : Fin d,
        (B.a x i j - (1 : Matrix (Fin d) (Fin d) ℝ) i j) ^ 2) ≤ 1 / 4) →
      ∀ (q : E → ℝ), ContDiff ℝ ∞ q →
      (∀ n ≤ m + d - 1, ∀ x ∈ V, ‖iteratedFDeriv ℝ n q x‖ ≤ Q) →
      ∀ {u f : E → ℝ}, ContDiffOn ℝ ∞ u O → ContDiffOn ℝ ∞ f O →
        WeakEquation V (matrixFlux B.a (fun j => partialDeriv j u))
          (fun x => f x + q x * u x) →
        ∀ x ∈ K, ‖iteratedFDeriv ℝ m u x‖ ≤ C *
          (derivativeProfile 2 V 0 u + derivativeProfile 2 V (m + d - 1) f).toReal := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_pointwise_jet_bound
    m hV hVc hVΩ hK hKV hκ hL hQ
  refine ⟨C, hC, ?_⟩
  intro B hB hjet hosc q hq hqjet u f hu hf heq x hx
  obtain ⟨v, hv, _, hvu⟩ := exists_smooth_compact_extension_near_compact hO hVc hVO hu
  obtain ⟨F, hF, _, hFf⟩ := exists_smooth_compact_extension_near_compact hO hVc hVO hf
  have hvg (y : E) (hy : y ∈ V) : v =ᶠ[𝓝 y] u := hvu y (subset_closure hy)
  have hFg (y : E) (hy : y ∈ V) : F =ᶠ[𝓝 y] f := hFf y (subset_closure hy)
  have heq' : WeakEquation V (matrixFlux B.a (fun j => partialDeriv j v))
      (fun y => F y + q y * v y) := by
    intro φ hφ hφc hφV
    calc
      (∫ y in V, ∑ i, matrixFlux B.a (fun j => partialDeriv j v) i y * partialDeriv i φ y) =
          ∫ y in V, ∑ i, matrixFlux B.a (fun j => partialDeriv j u) i y * partialDeriv i φ y := by
        apply setIntegral_congr_fun hV.measurableSet
        intro y hy
        have hd (j : Fin d) : partialDeriv j v y = partialDeriv j u y :=
          congrArg (fun A : E →L[ℝ] ℝ => A (EuclideanSpace.single j 1)) (hvg y hy).fderiv_eq
        simp only [matrixFlux, hd]
      _ = ∫ y in V, (f y + q y * u y) * φ y := heq φ hφ hφc hφV
      _ = ∫ y in V, (F y + q y * v y) * φ y := by
        apply setIntegral_congr_fun hV.measurableSet
        intro y hy
        change (f y + q y * u y) * φ y = (F y + q y * v y) * φ y
        rw [(hvg y hy).self_of_nhds, (hFg y hy).self_of_nhds]
  have h := hbound B hB hjet hosc q hq hqjet hv hF heq' x hx
  rw [derivativeProfile_eq_of_local_germs hV.measurableSet hvg 2 0,
    derivativeProfile_eq_of_local_germs hV.measurableSet hFg 2 (m + d - 1)] at h
  rwa [((hvg x (hKV hx)).iteratedFDeriv ℝ m).self_of_nhds] at h

#print axioms exists_smooth_compact_extension_near_compact
#print axioms derivativeProfile_eq_of_local_germs
#print axioms exists_local_uniform_pointwise_jet_bound

end Yamabe3.Analysis.UniformElliptic
