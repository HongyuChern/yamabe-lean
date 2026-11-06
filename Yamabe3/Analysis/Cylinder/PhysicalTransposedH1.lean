import Yamabe3.Analysis.Cylinder.NativeFiniteForcingBounds
import Yamabe3.Analysis.UniformElliptic.InhomogeneousBootstrap

/-!
# Genuine weak first derivatives turn the physical transposed equation into H1 form

Weak partials are tested against the actual smooth compact derivatives of
an arbitrary test. Their real integration-by-parts identities identify the
native Euclidean Laplacian pairing. The physical Jacobi source and potential
are then moved by actual integrable identities, with their true constants.
No weak derivative is inferred from an L2 transposed equation in this file.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Sobolev.Weak

theorem contDiffOn_physicalForcing {f : ℝ × S → ℝ}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞ (physicalForcing f) ({0}ᶜ : Set E) := by
  intro x hx
  have hx0 : x ≠ 0 := by simpa using hx
  exact ((contDiffAt_const.mul (contDiffAt_cylinderLift hf hx0)).div
    (contDiff_norm_sq ℝ).contDiffAt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx0))).contDiffWithinAt

theorem memLp_physicalPotential_mul_on_precompact {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) {V : Set E} (hV : MeasurableSet V)
    (hVc : IsCompact (closure V)) (hVO : closure V ⊆ ({0}ᶜ : Set E))
    {u : E → ℝ} (hu : MemLp u 2 (volume.restrict V)) :
    MemLp (fun x => physicalPotential v x * u x) 2 (volume.restrict V) := by
  obtain ⟨C, hC⟩ := hVc.exists_bound_of_continuousOn
    ((contDiffOn_physicalPotential hv).continuousOn.mono hVO)
  apply hu.of_le_mul (c := C)
    ((measurable_physicalPotential hv.continuous.measurable).aestronglyMeasurable.mul
      hu.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem hV] with x hx
  change ‖physicalPotential v x * u x‖ ≤ C * ‖u x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x (subset_closure hx)) (norm_nonneg _)

theorem memLp_native_euclidean_laplacian_test {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (V : Set E) :
    MemLp (euclideanD.laplacian φ) 2 (volume.restrict V) :=
  ((euclideanD.contMDiff_laplacian hφ.contMDiff).continuous.memLp_of_hasCompactSupport
    (euclideanD.hasCompactSupport_laplacian hc)).restrict V

/-- The actual H1 gradient pairing equals the actual native Euclidean
negative-Laplacian pairing for every smooth compact test. -/
theorem gradient_pairing_eq_negative_laplacian {V : Set E}
    {u : E → ℝ} {p : Fin 3 → E → ℝ}
    (hu : MemLp u 2 (volume.restrict V))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict V))
    (hpartial : ∀ i, HasWeakPartialDeriv i (p i) u V)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ V) :
    (∫ x in V, ∑ i : Fin 3, p i x * partialDeriv i φ x) =
      ∫ x in V, u x * (-euclideanD.laplacian φ x) := by
  have hfirst (i : Fin 3) : MemLp (partialDeriv i φ) 2 (volume.restrict V) :=
    ((contDiff_partial hφ i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_partial hc i)).restrict V
  have hsecond (i : Fin 3) : MemLp (partialDeriv i (partialDeriv i φ))
      2 (volume.restrict V) :=
    ((contDiff_partial (contDiff_partial hφ i) i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_partial (hasCompactSupport_partial hc i) i)).restrict V
  have hibp (i : Fin 3) :
      (∫ x in V, p i x * partialDeriv i φ x) =
        -(∫ x in V, u x * partialDeriv i (partialDeriv i φ) x) := by
    have h := hpartial i (partialDeriv i φ) (contDiff_partial hφ i)
      (hasCompactSupport_partial hc i) ((tsupport_partial_subset i φ).trans hs)
    change (∫ x in V, u x * partialDeriv i (partialDeriv i φ) x) =
      -(∫ x in V, p i x * partialDeriv i φ x) at h
    linarith
  rw [integral_finsetSum Finset.univ
    (f := fun i x => p i x * partialDeriv i φ x)
    (fun i _ => (hp i).integrable_mul (hfirst i))]
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum Finset.univ
    (f := fun i x => u x * partialDeriv i (partialDeriv i φ) x)
    (fun i _ => hu.integrable_mul (hsecond i)), ← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change -(∑ i : Fin 3, u x * partialDeriv i (partialDeriv i φ) x) =
      u x * (-euclideanD.laplacian φ x)
    rw [euclidean_laplacian_eq_partial_trace (hφ.contDiffAt)]
    rw [← Finset.mul_sum]
    ring

/-- Once the genuine L2 weak partials have been constructed, the genuine
physical Jacobi transposed equation gives the real divergence weak equation. -/
theorem weakEquation_of_native_transposedJacobi {V : Set E}
    (hVzero : V ⊆ ({0}ᶜ : Set E))
    (v : ℝ → ℝ) (u : E → ℝ) (f : ℝ × S → ℝ) (p : Fin 3 → E → ℝ)
    (hu : MemLp u 2 (volume.restrict V))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict V))
    (hpartial : ∀ i, HasWeakPartialDeriv i (p i) u V)
    (hF : MemLp (physicalForcing f) 2 (volume.restrict V))
    (hQ : MemLp (fun x => physicalPotential v x * u x) 2 (volume.restrict V))
    (htest : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → 0 ∉ tsupport φ →
      (∫ x : E, u x * physicalJacobi v φ x) = ∫ x : E, physicalForcing f x * φ x) :
    WeakEquation V (matrixFlux (euclideanPrincipalForm V).a p)
      (physicalPrincipalForcing v u f) := by
  intro φ hφ hc hs
  have hzero : 0 ∉ tsupport φ := fun h => by simpa using hVzero (hs h)
  have hφL : MemLp φ 2 (volume.restrict V) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).restrict V
  have hLap : Integrable (fun x => u x * (-euclideanD.laplacian φ x))
      (volume.restrict V) := hu.integrable_mul (memLp_native_euclidean_laplacian_test hφ hc V).neg
  have hpot : Integrable (fun x => physicalPotential v x * u x * φ x)
      (volume.restrict V) := hQ.integrable_mul hφL
  have hsrc : Integrable (fun x => physicalForcing f x * φ x)
      (volume.restrict V) := hF.integrable_mul hφL
  have hraw : (∫ x in V, u x * physicalJacobi v φ x) =
      ∫ x in V, physicalForcing f x * φ x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hφx := image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))
      have hΔx := image_eq_zero_of_notMem_tsupport
        (fun ht => hx (hs (euclideanD.tsupport_laplacian_subset φ ht)))
      simp only [physicalJacobi, hφx, hΔx, mul_zero, sub_zero, add_zero]),
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), mul_zero])]
    exact htest φ hφ hc hzero
  have hleft : (∫ x in V, u x * physicalJacobi v φ x) =
      8 * (∫ x in V, u x * (-euclideanD.laplacian φ x)) -
      8 * (∫ x in V, physicalPotential v x * u x * φ x) := by
    calc
      _ = ∫ x in V, 8 * (u x * (-euclideanD.laplacian φ x)) -
          8 * (physicalPotential v x * u x * φ x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          simp only [physicalJacobi, physicalPotential, euclidean_scalarCurvature_zero,
            zero_mul, add_zero]
          ring
      _ = _ := by rw [integral_sub (hLap.const_mul _) (hpot.const_mul _),
        integral_const_mul, integral_const_mul]
  have hright : (∫ x in V, physicalPrincipalForcing v u f x * φ x) =
      (∫ x in V, physicalForcing f x * φ x) / 8 +
      ∫ x in V, physicalPotential v x * u x * φ x := by
    calc
      _ = ∫ x in V, (physicalForcing f x * φ x) / 8 +
          physicalPotential v x * u x * φ x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp only [physicalPrincipalForcing, physicalPotential]
          ring
      _ = _ := by rw [integral_add (hsrc.div_const _) hpot, integral_div]
  calc
    _ = ∫ x in V, ∑ i : Fin 3, p i x * partialDeriv i φ x := by
      simp [euclideanPrincipalForm, matrixFlux, Matrix.one_apply]
    _ = ∫ x in V, u x * (-euclideanD.laplacian φ x) :=
      gradient_pairing_eq_negative_laplacian hu hp hpartial hφ hc hs
    _ = _ := by rw [hright]; linarith [hleft, hraw]

#print axioms gradient_pairing_eq_negative_laplacian
#print axioms weakEquation_of_native_transposedJacobi

end Yamabe3.Analysis.SpherePolar
