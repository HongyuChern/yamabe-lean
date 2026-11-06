import Yamabe3.Analysis.NativeForcedRegularity
import Yamabe3.Analysis.NativeLocalForcedEquation

/-!
# The same native H1 inverse for a source smooth only on the open domain

A compact smooth extension of the actual source germ is chosen only in a
proof neighborhood. Tests supported there have exactly the same forcing
integral. The proved global-smooth-source local regularity theorem therefore
produces representatives of the original H1 element, which glue using the
native measure. The native local forced equation then identifies their
pointwise PDE, again with the original source.

There is no assumption that the source is globally smooth or globally L2,
no new weak inverse and no change to the represented H1 element. This source
is a candidate pending compilation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g}

private theorem exists_source_germ_neighborhood
    {Ω : Set M} (hΩ : IsOpen Ω) {F : M → ℝ}
    (hF : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ F Ω) {x : M} (hx : x ∈ Ω) :
    ∃ (V : Set M) (F₀ : M → ℝ), IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F₀ ∧ EqOn F₀ F V := by
  obtain ⟨F₀, hF₀, -, -, hsame⟩ := exists_compact_smooth_germ hΩ hF hx
  obtain ⟨V, hsub, hV, hxV⟩ := mem_nhds_iff.mp (inter_mem (hΩ.mem_nhds hx) hsame)
  exact ⟨V, F₀, hV, hxV, fun y hy => (hsub hy).1, hF₀,
    fun y hy => (hsub hy).2⟩

private theorem integral_test_eq_of_source_germ
    {V : Set M} (hV : IsOpen V) {F₀ F φ : M → ℝ}
    (heq : EqOn F₀ F V) (hs : tsupport φ ⊆ V) :
    (∫ y, φ y * F y ∂g.volumeMeasure) = ∫ y, φ y * F₀ y ∂g.volumeMeasure := by
  apply integral_mul_eq_of_ae_eq_on hV _ hs
  exact (ae_restrict_iff' hV.measurableSet).mpr (ae_of_all _ fun y hy => (heq hy).symm)

variable [CompactSpace M]

/-- Genuine native regularity for a source smooth only in the open domain.
The representative and the pointwise forced equation belong to the very
same completed H1 element that occurs in all of the native test identities. -/
theorem exists_native_smooth_representative_of_locally_smooth_forcing
    (hn : 0 < n) {Ω : Set M} (hΩ : IsOpen Ω)
    (V F : M → ℝ)
    (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V)
    (hF : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ F Ω)
    (w : H1Zero D univ)
    (hweak : ∀ φ : EnergyTest D univ, tsupport (φ : M → ℝ) ⊆ Ω →
      (∫ y, (-D.laplacian φ y + V y * φ y) * toL2 D univ w y ∂g.volumeMeasure) =
        ∫ y, φ y * F y ∂g.volumeMeasure) :
    ∃ U : M → ℝ, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U Ω ∧
      U =ᵐ[g.volumeMeasure.restrict Ω] (toL2 D univ w : M → ℝ) ∧
      ∀ x ∈ Ω, -D.laplacian U x + V x * U x = F x := by
  have hlocal : ∀ x ∈ Ω, ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ O ⊆ Ω ∧
      ∃ U : M → ℝ, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U O ∧
        U =ᵐ[g.volumeMeasure.restrict O] (toL2 D univ w : M → ℝ) := by
    intro x hx
    obtain ⟨O, F₀, hO, hxO, hOΩ, hF₀, hsame⟩ :=
      exists_source_germ_neighborhood hΩ hF hx
    have hweak₀ (φ : EnergyTest D univ) (hs : tsupport (φ : M → ℝ) ⊆ O) :
        (∫ y, (-D.laplacian φ y + V y * φ y) * toL2 D univ w y ∂g.volumeMeasure) =
          ∫ y, φ y * F₀ y ∂g.volumeMeasure :=
      (hweak φ (hs.trans hOΩ)).trans (integral_test_eq_of_source_germ hO hsame hs)
    obtain ⟨U, hUs, hUae⟩ := exists_smooth_representative_of_native_smooth_forced
      hn hO V F₀ hV hF₀ w hweak₀
    exact ⟨O, hO, hxO, hOΩ, U, hUs, hUae⟩
  obtain ⟨U, hUs, hUae⟩ :=
    exists_smooth_representative_of_local hΩ (toL2 D univ w) hlocal
  have hweakU (φ : EnergyTest D Ω) :
      (∫ y, (-D.laplacian φ y + V y * φ y) * U y ∂g.volumeMeasure) =
        ∫ y, φ y * F y ∂g.volumeMeasure := by
    let φ₀ : EnergyTest D univ :=
      ⟨(φ : M → ℝ), φ.smooth, φ.hasCompactSupport, subset_univ _⟩
    calc
      _ = ∫ y, (-D.laplacian φ y + V y * φ y) * toL2 D univ w y ∂g.volumeMeasure := by
        apply integral_congr_ae
        have hae := (ae_restrict_iff' hΩ.measurableSet).mp hUae
        filter_upwards [hae] with y hy
        by_cases hyΩ : y ∈ Ω
        · rw [hy hyΩ]
        · have hyφ : y ∉ tsupport (φ : M → ℝ) := fun hz => hyΩ (φ.support_subset hz)
          have hφy : φ y = 0 := image_eq_zero_of_notMem_tsupport hyφ
          have hΔ : D.laplacian φ y = 0 := image_eq_zero_of_notMem_tsupport
            (fun hz => hyφ (D.tsupport_laplacian_subset φ hz))
          simp only [hφy, hΔ, neg_zero, mul_zero, add_zero, zero_mul]
      _ = _ := hweak φ₀ φ.support_subset
  refine ⟨U, hUs, hUae, ?_⟩
  intro x hx
  obtain ⟨O, F₀, hO, hxO, hOΩ, hF₀, hsame⟩ :=
    exists_source_germ_neighborhood hΩ hF hx
  have hweak₀ (φ : EnergyTest D O) :
      (∫ y, (-D.laplacian φ y + V y * φ y) * U y ∂g.volumeMeasure) =
        ∫ y, φ y * F₀ y ∂g.volumeMeasure := by
    let φΩ : EnergyTest D Ω :=
      ⟨(φ : M → ℝ), φ.smooth, φ.hasCompactSupport, φ.support_subset.trans hOΩ⟩
    exact (hweakU φΩ).trans
      (integral_test_eq_of_source_germ hO hsame φ.support_subset)
  have heq := native_schrodinger_eq_source_of_smooth_transposed D hO hV hF₀
    (hUs.mono hOΩ) hweak₀ x hxO
  exact heq.trans (hsame hxO)

#print axioms exists_native_smooth_representative_of_locally_smooth_forcing

end Yamabe3.Analysis
