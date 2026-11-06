import Yamabe3.Analysis.SobolevLocalPullback

/-! A fixed cutoff gives an actual compact Sobolev extension on the
retained compact set. Its norm constant precedes the input function. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.BoundaryLocalization
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_bounded_compact_sobolev_extension (k : ℕ)
    {K W : Set E} (hK : IsCompact K) (hW : IsOpen W) (hKW : K⊆W) :
    ∃ C : ℝ≥0∞,C≠⊤ ∧ ∀ u : E → ℝ,MemWkp k 2 u W →
      ∃ v : E → ℝ,HasCompactSupport v ∧ MemWkp k 2 v univ ∧ EqOn v u K ∧
        iteratedWeakSobolevNorm k 2 v univ≤C*iteratedWeakSobolevNorm k 2 u W := by
  obtain ⟨χ,hχ,hχc,-,hone,hs⟩ :=
    Poincare.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff hK hW hKW
  obtain ⟨C,hC,hb⟩ := exists_localized_sobolev_multiplier_bound k isOpen_univ hW χ hχ hχc hs
  refine ⟨C,hC,?_⟩
  intro u hu
  have hu' : MemWkp k 2 u (W∩univ) := by simpa only [inter_univ] using hu
  refine ⟨fun x => χ x*u x,hχc.mul_right,
    memWkp_mul_smooth_of_tsupport_subset k isOpen_univ hW hu' hχ hχc hs,?_,?_⟩
  · intro x hx
    simp only [hone x hx,one_mul]
  · simpa only [inter_univ] using hb u hu'

#print axioms exists_bounded_compact_sobolev_extension
end Yamabe3.Analysis.UniformElliptic
