import Yamabe3.Analysis.SobolevSmoothPullback

/-! Smooth compact extensions of a smooth map near a fixed compact set.
Only the original map on that compact set is retained by later consumers. -/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A compact cutoff gives a globally smooth extension equal to the original
map on K. The original map need not be regular outside its open domain. -/
theorem exists_smooth_map_eq_on_compact
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S K : Set E} (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f S) :
    ∃ Φ : E → F, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧ EqOn Φ f K := by
  obtain ⟨χ, hχ, hc, -, hone, hs⟩ :=
    Poincare.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff hK hS hKS
  let Φ : E → F := fun x => χ x • f x
  refine ⟨Φ, ?_, hc.smul_right, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ S
    · exact hχ.contDiffAt.smul ((hf x hx).contDiffAt (hS.mem_nhds hx))
    · have ht : x ∉ tsupport χ := fun h => hx (hs h)
      have he : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp ht
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [he] with y hy
      change χ y • f y = 0
      rw [show χ y = 0 from hy, zero_smul]
  · intro x hx
    change χ x • f x = f x
    rw [hone x hx, one_smul]

#print axioms exists_smooth_map_eq_on_compact
end Yamabe3.Analysis.UniformElliptic
