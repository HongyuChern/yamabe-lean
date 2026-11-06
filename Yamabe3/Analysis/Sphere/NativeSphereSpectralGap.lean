import Yamabe3.Analysis.Sphere.NativeSphereLoweringEquation
import Yamabe3.Analysis.Sphere.NativeCompactSpectrum
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The genuine low spectrum and high-mode gap of the round two-sphere

Twice applying the actual lowering equation and the compact native eigenvalue
sign excludes eigenvalues in (0,2) and (2,6).  The zero eigenspace is constant,
and the eigenvalue-two eigenspace consists exactly of ambient height functions.
No classification of spherical harmonics or spectral gap is a premise.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SphereSpectrum

open Poincare.Geometry.Riemannian.SpaceForm

theorem exists_nonneg_spherical_root {μ : ℝ} (hμ : 0 ≤ μ) :
    ∃ α : ℝ, 0 ≤ α ∧ α * (α + 1) = μ := by
  have hpos : 0 ≤ 1 + 4 * μ := by linarith
  have hs := Real.sq_sqrt hpos
  have hn := Real.sqrt_nonneg (1 + 4 * μ)
  have h1 : 1 ≤ Real.sqrt (1 + 4 * μ) := by nlinarith
  refine ⟨(Real.sqrt (1 + 4 * μ) - 1) / 2, by linarith, ?_⟩
  nlinarith

theorem not_native_eigenvalue_between_zero_two
    (D : LeviCivitaData (roundSphereMetric 2)) {f : UnitSphere 2 → ℝ} {μ : ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (hne : ∃ x, f x ≠ 0)
    (heigen : ∀ x, -D.laplacian f x = μ * f x) (hμ : 0 < μ) (hμ2 : μ < 2) : False := by
  obtain ⟨α, hα, hroot⟩ := exists_nonneg_spherical_root hμ.le
  have hαpos : 0 < α := by nlinarith
  have hα1 : α < 1 := by nlinarith
  obtain ⟨a, x, hx⟩ := exists_lowering_ne_zero D hαpos.ne' hne
  have he : ∀ y, -D.laplacian (lowering D f α a) y = α * (α - 1) * lowering D f α a y :=
    lowering_eigen_equation D hf (by simpa only [hroot] using heigen) a
  have hnonneg := native_eigenvalue_nonneg D (smooth_lowering D hf α a) ⟨x, hx⟩ he
  have hneg : α * (α - 1) < 0 := mul_neg_of_pos_of_neg hαpos (by linarith)
  exact (not_lt_of_ge hnonneg) hneg

theorem native_eigenvalue_zero_two_or_ge_six
    (D : LeviCivitaData (roundSphereMetric 2)) {f : UnitSphere 2 → ℝ} {μ : ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (hne : ∃ x, f x ≠ 0)
    (heigen : ∀ x, -D.laplacian f x = μ * f x) : μ = 0 ∨ μ = 2 ∨ 6 ≤ μ := by
  have hμ := native_eigenvalue_nonneg D hf hne heigen
  by_cases h0 : μ = 0
  · exact Or.inl h0
  have hpos : 0 < μ := lt_of_le_of_ne hμ (Ne.symm h0)
  have h2 : 2 ≤ μ := by
    by_contra hfail
    exact not_native_eigenvalue_between_zero_two D hf hne heigen hpos (lt_of_not_ge hfail)
  by_cases htwo : μ = 2
  · exact Or.inr (Or.inl htwo)
  refine Or.inr (Or.inr ?_)
  by_contra hfail
  have h6 : μ < 6 := lt_of_not_ge hfail
  have hgt2 : 2 < μ := lt_of_le_of_ne h2 (Ne.symm htwo)
  obtain ⟨α, hα, hroot⟩ := exists_nonneg_spherical_root hμ
  have hα1 : 1 < α := by nlinarith
  have hα2 : α < 2 := by nlinarith
  obtain ⟨a, x, hx⟩ := exists_lowering_ne_zero D (by linarith) hne
  have he : ∀ y, -D.laplacian (lowering D f α a) y = α * (α - 1) * lowering D f α a y :=
    lowering_eigen_equation D hf (by simpa only [hroot] using heigen) a
  apply not_native_eigenvalue_between_zero_two D (smooth_lowering D hf α a) ⟨x, hx⟩ he
  · exact mul_pos (by linarith) (by linarith)
  · nlinarith

theorem roundTwoSphere_connected : IsConnected (Metric.sphere (0 : Ambient 2) 1) :=
  isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [Ambient])) 0 zero_le_one

theorem native_harmonic_on_roundTwoSphere
    (D : LeviCivitaData (roundSphereMetric 2)) {f : UnitSphere 2 → ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (heigen : ∀ x, -D.laplacian f x = 0) :
    ∃ c : ℝ, ∀ x, f x = c := by
  let : PreconnectedSpace (UnitSphere 2) :=
    Subtype.preconnectedSpace roundTwoSphere_connected.isPreconnected
  obtain ⟨p, hp⟩ := roundTwoSphere_connected.nonempty
  let q : UnitSphere 2 := ⟨p, hp⟩
  exact ⟨f q, native_harmonic_eq_constant D hf (fun x => neg_eq_zero.mp (heigen x)) q⟩

theorem native_eigenvalue_two_is_height
    (D : LeviCivitaData (roundSphereMetric 2)) {f : UnitSphere 2 → ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (heigen : ∀ x, -D.laplacian f x = 2 * f x) :
    ∃ a : Ambient 2, f = height a := by
  let : PreconnectedSpace (UnitSphere 2) :=
    Subtype.preconnectedSpace roundTwoSphere_connected.isPreconnected
  obtain ⟨p, hp⟩ := roundTwoSphere_connected.nonempty
  let q : UnitSphere 2 := ⟨p, hp⟩
  let V : Ambient 2 := mfderiv (𝓡 2) (𝓡 3) (Subtype.val : UnitSphere 2 → Ambient 2) q
    (D.gradient f q)
  have hconst (a : Ambient 2) : ∀ x, lowering D f 1 a x = lowering D f 1 a q := by
    apply native_harmonic_eq_constant D (smooth_lowering D hf 1 a)
    intro x
    have h := lowering_eigen_equation D (α := 1) hf (by intro y; convert heigen y using 1 <;> ring) a x
    simpa using h
  refine ⟨V + f q • (q : Ambient 2), ?_⟩
  funext x
  have h := hconst (x : Ambient 2) x
  rw [lowering_self, one_mul, lowering, inner_gradient_height] at h
  change f x = inner ℝ (x : Ambient 2) V + 1 * inner ℝ (x : Ambient 2) (q : Ambient 2) * f q at h
  rw [h]
  simp only [height, inner_add_left, real_inner_smul_left]
  rw [real_inner_comm V (x : Ambient 2), real_inner_comm (q : Ambient 2) (x : Ambient 2)]
  ring

#print axioms native_eigenvalue_zero_two_or_ge_six
#print axioms native_harmonic_on_roundTwoSphere
#print axioms native_eigenvalue_two_is_height

end Yamabe3.Analysis.SphereSpectrum
