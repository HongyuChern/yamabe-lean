import Yamabe3.Analysis.UniformElliptic.LocalUniformJet
import Yamabe3.Analysis.UniformElliptic.UniformCaccioppoli

/-!
# Local Caccioppoli estimates with constructed smooth extensions

The native spectral approximants are smooth only off the origin. This
module builds genuine compact smooth extensions near the fixed integration
sets before applying the uniform energy estimate. No global regularity of
an infinite representative or of an unextended approximant is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem memLp_of_local_smooth_precompact {O V : Set E}
    (hO : IsOpen O) (hV : MeasurableSet V) (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u O) : MemLp u 2 (volume.restrict V) := by
  obtain ⟨v, hv, hvc, hvg⟩ := exists_smooth_compact_extension_near_compact hO hVc hVO hu
  apply ((hv.continuous.memLp_of_hasCompactSupport (p := 2) hvc).restrict V).ae_eq
  filter_upwards [ae_restrict_mem hV] with x hx
  exact (hvg x (subset_closure hx)).self_of_nhds

theorem memLp_partial_of_local_smooth_precompact {O V : Set E}
    (hO : IsOpen O) (hV : MeasurableSet V) (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u O) (w : E) :
    MemLp (fun x => fderiv ℝ u x w) 2 (volume.restrict V) := by
  obtain ⟨v, hv, hvc, hvg⟩ := exists_smooth_compact_extension_near_compact hO hVc hVO hu
  have hl : MemLp (fun x => fderiv ℝ v x w) 2 volume :=
    ((hv.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hvc.fderiv_apply ℝ w)
  apply (hl.restrict V).ae_eq
  filter_upwards [ae_restrict_mem hV] with x hx
  exact congrArg (fun A : E →L[ℝ] ℝ => A w) (hvg x (subset_closure hx)).fderiv_eq

/-- The numerical constant is selected before the coefficient field and
before every locally smooth approximant. The global smooth function needed
by the energy proof is constructed internally with the same local germs. -/
theorem exists_local_uniform_gradient_integral_le [NeZero d]
    {Ω O V W : Set E} (hO : IsOpen O) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O) (hVΩ : V ⊆ Ω)
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V)
    {κ A : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : SmoothEllipticBilinearForm d Ω), κ ≤ B.lam →
      (∀ x ∈ V, ∀ i j : Fin d, |B.a x i j| ≤ A) →
      ∀ {u f : E → ℝ}, ContDiffOn ℝ ∞ u O →
        MemLp u 2 (volume.restrict V) → MemLp f 2 (volume.restrict V) →
        WeakEquation V (matrixFlux B.a (fun j => partialDeriv j u)) f →
        (∫ x in W, ∑ i : Fin d, (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2) ≤
          C * ((∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_gradient_integral_le_on_nested_sets
    hV hVΩ hW hWc hWV hκ hA
  refine ⟨C, hC, ?_⟩
  intro B hB ha u f hu hum hfm heq
  obtain ⟨v, hv, hvc, hvg⟩ := exists_smooth_compact_extension_near_compact hO hVc hVO hu
  have hg (x : E) (hx : x ∈ V) : v =ᶠ[𝓝 x] u := hvg x (subset_closure hx)
  have hvm : MemLp v 2 (volume.restrict V) :=
    (hv.continuous.memLp_of_hasCompactSupport (p := 2) hvc).restrict V
  have heq' : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ x in V, B.principalIntegrand v φ x) = ∫ x in V, f x * φ x := by
    intro φ hφ hφc hφV
    have h := heq φ hφ hφc hφV
    convert h using 1
    apply setIntegral_congr_fun hV.measurableSet
    intro x hx
    simp only [SmoothEllipticBilinearForm.principalIntegrand, matrixFlux,
      partialDeriv, (hg x hx).fderiv_eq, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [B.symm]
  have h := hbound B hB ha hv hvm hfm heq'
  have hval : (∫ x in V, v x ^ 2) = ∫ x in V, u x ^ 2 := by
    apply setIntegral_congr_fun hV.measurableSet
    intro x hx
    dsimp only
    rw [(hg x hx).self_of_nhds]
  have hgrad : (∫ x in W, ∑ i : Fin d, (fderiv ℝ v x (EuclideanSpace.single i 1)) ^ 2) =
      ∫ x in W, ∑ i : Fin d, (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2 := by
    apply setIntegral_congr_fun hW.measurableSet
    intro x hx
    dsimp only
    rw [(hg x (hWV (subset_closure hx))).fderiv_eq]
  rwa [hval, hgrad] at h

#print axioms memLp_partial_of_local_smooth_precompact
#print axioms exists_local_uniform_gradient_integral_le

end Yamabe3.Analysis.UniformElliptic
