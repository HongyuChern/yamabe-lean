import Yamabe3.Analysis.Green.NativeSchrodingerMaximum
import PoincareLib.Geometry.Riemannian.ScalarOperators.Product

/-!
# Elementary native spectral facts on a closed manifold

The sign of an actual smooth eigenvalue follows from the squared function at
its compact maximum.  The zero eigenspace on a connected compact background
consists of constants by the previously proved native strong maximum principle.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareMT
open scoped Manifold ContDiff Bundle Topology

namespace Yamabe3.Analysis.SphereSpectrum

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] {g : RiemannianMetric n M}

theorem native_eigenvalue_nonneg (D : LeviCivitaData g) {f : M → ℝ} {μ : ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hne : ∃ x, f x ≠ 0)
    (heigen : ∀ x, -D.laplacian f x = μ * f x) : 0 ≤ μ := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨q, _, hq⟩ := isCompact_univ.exists_isMaxOn (f := fun y => (f y) ^ 2)
    ⟨x, mem_univ x⟩ (hf.continuous.pow 2).continuousOn
  have hqpos : 0 < (f q) ^ 2 := (sq_pos_of_ne_zero hx).trans_le (hq (mem_univ x))
  have hlocal : IsLocalMax (fun y => (f y) ^ 2) q :=
    Filter.Eventually.of_forall (fun y => hq (mem_univ y))
  have hΔ := D.laplacian_nonpos_of_isLocalMax (hf.pow 2) hlocal
  rw [D.laplacian_sq hf] at hΔ
  have hgrad : 0 ≤ g.inner q (D.gradient f q) (D.gradient f q) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change 0 ≤ inner ℝ (D.gradient f q) (D.gradient f q)
    exact real_inner_self_nonneg
  have he : D.laplacian f q = -μ * f q := by linarith [heigen q]
  rw [he] at hΔ
  by_contra hn
  have hμ : μ < 0 := lt_of_not_ge hn
  have hp : 0 < -μ * (f q) ^ 2 := mul_pos (neg_pos.mpr hμ) hqpos
  nlinarith

theorem native_harmonic_eq_constant [PreconnectedSpace M]
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hharm : ∀ x, D.laplacian f x = 0) (p : M) : ∀ x, f x = f p := by
  obtain ⟨q, _, hq⟩ := isCompact_univ.exists_isMaxOn (f := f)
    ⟨p, mem_univ p⟩ hf.continuous.continuousOn
  have hΔc (c : ℝ) (x : M) : D.laplacian (fun _ : M => c) x = 0 := by
    simp [LeviCivitaData.laplacian, LeviCivitaData.hessian,
      LeviCivitaData.hessianOnFields, mvfderiv_const]
  have hzero := D.eq_zero_of_nonpos_laplacian_ge_mul_on 0 le_rfl isOpen_univ
    isPreconnected_univ (hf.sub contMDiff_const).contMDiffOn
    (fun x _ => sub_nonpos.mpr (hq (mem_univ x)))
    (by
      intro x _
      rw [D.laplacian_sub hf contMDiff_const, hharm, hΔc]
      simp)
    (mem_univ q) (sub_self (f q))
  have he (x : M) : f x = f q := sub_eq_zero.mp (hzero x (mem_univ x))
  intro x
  rw [he x, he p]

#print axioms native_eigenvalue_nonneg
#print axioms native_harmonic_eq_constant

end Yamabe3.Analysis.SphereSpectrum
