import Yamabe3.Analysis.SobolevSmoothPullback
import Yamabe3.Analysis.SobolevNormLimits

/-! A controlled smooth sequence for the actual compactly supported input.
Both the genuine jets and the full norm converge to that same input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem sobolev_norm_sub_comm {O : Set E} (hO : IsOpen O) (k : ℕ)
    {u v : E → ℝ} (hu : MemWkp k 2 u O) (hv : MemWkp k 2 v O) :
    iteratedWeakSobolevNorm k 2 (fun x => u x - v x) O =
      iteratedWeakSobolevNorm k 2 (fun x => v x - u x) O := by
  have h := wkpNorm_const_smul (by norm_num : (1 : ℝ≥0∞) ≤ 2) hO
    (MemWkp.sub (by norm_num) hO hv hu) (-1)
  simpa only [neg_one_mul, neg_sub, enorm_neg, enorm_one, one_mul] using h

/-- A nonnegative geometric error, tending to zero. -/
def sobolevApproxError (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ)^n)

theorem sobolevApproxError_tendsto : Tendsto sobolevApproxError atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / 2 : ℝ)^n)) atTop (𝓝 0)
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.tendsto 0).comp
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num))

/-- Density with quantitative two-sided error and genuine norm convergence. -/
theorem exists_smooth_sobolev_sequence [NeZero d] (k : ℕ) {u : E → ℝ}
    (hu : MemWkp k 2 u univ) (huc : HasCompactSupport u) :
    ∃ φ : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ ∞ (φ n) ∧ HasCompactSupport (φ n) ∧ MemWkp k 2 (φ n) univ) ∧
      (∀ n, iteratedWeakSobolevNorm k 2 (fun x => φ n x - u x) univ ≤ sobolevApproxError n) ∧
      Tendsto (fun n => iteratedWeakSobolevNorm k 2 (φ n) univ) atTop
        (𝓝 (iteratedWeakSobolevNorm k 2 u univ)) := by
  classical
  have hex (n : ℕ) := MemWkp.exists_smooth_compactSupport_approx isOpen_univ k 2
    (by norm_num) (by norm_num) hu huc (subset_univ _) ((1/2 : ℝ)^n) (by positivity)
  choose φ hφ hc hs hb using hex
  have hm (n : ℕ) : MemWkp k 2 (φ n) univ :=
    MemWkp_of_smooth_compactSupport isOpen_univ (hφ n) (hc n) (hs n) (by norm_num) k
  have hb' (n : ℕ) : iteratedWeakSobolevNorm k 2 (fun x => φ n x - u x) univ ≤ sobolevApproxError n := by
    rw [sobolev_norm_sub_comm isOpen_univ k (hm n) hu]
    exact hb n
  refine ⟨φ, fun n => ⟨hφ n, hc n, hm n⟩, hb', ?_⟩
  apply sobolevNorm_tendsto_of_jet_limits hm hu
  intro j β hj
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds sobolevApproxError_tendsto
    (fun _ => zero_le)
    (fun n => (jet_difference_le_sobolev_difference isOpen_univ hj β (hm n) hu).trans (hb' n))

#print axioms exists_smooth_sobolev_sequence
end Yamabe3.Analysis.UniformElliptic
