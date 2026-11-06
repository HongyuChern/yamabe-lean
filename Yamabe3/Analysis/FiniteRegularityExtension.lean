import Yamabe3.Analysis.UniformElliptic.LocalUniformJet

/-! Compact localization preserves finite regularity and the actual germ.
This version makes no unjustified C-infinity assumption on an H4 solution. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.NirenbergEuclidean
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_finite_compact_extension_near_compact
    (n : ℕ) {O K : Set E} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {u : E → ℝ} (hu : ContDiffOn ℝ n u O) :
    ∃ v : E → ℝ, ContDiff ℝ n v ∧ HasCompactSupport v ∧
      ∀ x ∈ K, v =ᶠ[𝓝 x] u := by
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  obtain ⟨η, hη, hηc, _, hηone, hηO⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff (hK.cthickening (r := δ)) hO hδO
  refine ⟨fun x => η x * u x, ?_, hηc.mul_right, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ O
    · exact (hη.of_le (by exact_mod_cast le_top)).contDiffAt.mul (hu.contDiffAt (hO.mem_nhds hx))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have hz := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hηO h))
      filter_upwards [hz] with y hy
      simp [hy]
  · intro x hx
    filter_upwards [isOpen_thickening.mem_nhds (self_subset_thickening hδ K hx)] with y hy
    rw [hηone y (thickening_subset_cthickening δ K hy), one_mul]


#print axioms exists_finite_compact_extension_near_compact
end Yamabe3.Analysis.UniformElliptic
