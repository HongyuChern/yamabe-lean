import Yamabe3.Analysis.WeakLaplacianSobolev
import Yamabe3.Analysis.SobolevApproximationSequence

/-! Norm continuity of the actual weak flat operator on a fixed local
Sobolev domain. Coefficient-dependent constants here are used only to
pass a fixed operator to the limit, not as parameter-uniform estimates. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.BoundaryLocalization
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem sobolevNorm_sub_le {O : Set E} (hO : IsOpen O) {k : ℕ}
    {u v : E → ℝ} (hu : MemWkp k 2 u O) (hv : MemWkp k 2 v O) :
    iteratedWeakSobolevNorm k 2 (fun x => u x-v x) O ≤
      iteratedWeakSobolevNorm k 2 u O + iteratedWeakSobolevNorm k 2 v O := by
  have hvn := MemWkp.const_smul (by norm_num : (1:ℝ≥0∞) ≤ 2) hO hv (-1)
  have hh := wkpNorm_add_le (by norm_num : (1:ℝ≥0∞) ≤ 2) hO hu hvn
  rw [wkpNorm_const_smul (by norm_num) hO hv (-1)] at hh
  simpa only [neg_one_mul, ← sub_eq_add_neg, enorm_neg, enorm_one, one_mul] using hh

theorem sobolevNorm_tendsto_of_difference {O : Set E} (hO : IsOpen O)
    {k : ℕ} {u : ℕ → E → ℝ} {U : E → ℝ}
    (hu : ∀ n, MemWkp k 2 (u n) O) (hU : MemWkp k 2 U O)
    (ht : Tendsto (fun n => iteratedWeakSobolevNorm k 2 (fun x => u n x-U x) O) atTop (𝓝 0)) :
    Tendsto (fun n => iteratedWeakSobolevNorm k 2 (u n) O) atTop
      (𝓝 (iteratedWeakSobolevNorm k 2 U O)) := by
  apply sobolevNorm_tendsto_of_jet_limits hu hU
  intro j β hj
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
    (fun n => jet_difference_le_sobolev_difference hO hj β (hu n) hU)

def weakFlatOperator (O : Set E) (q u : E → ℝ) : E → ℝ :=
  fun x => weakNegativeLaplacian O u x-q x*u x

theorem weakFlatOperator_mem {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (k : ℕ) {q u : E → ℝ} (hq : ContDiff ℝ ∞ q) (hu : MemWkp (k+2) 2 u O) :
    MemWkp k 2 (weakFlatOperator O q u) O :=
  MemWkp.sub (by norm_num) hO (weakNegativeLaplacian_mem_bound hO k hu).1
    (memWkp_mul_smooth_of_isCompact_closure k hO hOc (hu.le_of_le (by omega)) hq)

theorem exists_weakFlatOperator_difference_bound
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (k : ℕ) (q : E → ℝ) (hq : ContDiff ℝ ∞ q) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u v : E → ℝ,
      MemWkp (k+2) 2 u O → MemWkp (k+2) 2 v O →
      iteratedWeakSobolevNorm k 2
        (fun x => weakFlatOperator O q u x-weakFlatOperator O q v x) O ≤
          C*iteratedWeakSobolevNorm (k+2) 2 (fun x => u x-v x) O := by
  obtain ⟨B,hB,hb⟩ := exists_compact_sobolev_multiplier_bound k hO hOc q hq
  refine ⟨(d:ℝ≥0∞)+B, by finiteness, ?_⟩
  intro u v hu hv
  have hd := MemWkp.sub (by norm_num : (1:ℝ≥0∞) ≤ 2) hO hu hv
  have hlu := (weakNegativeLaplacian_mem_bound hO k hu).1
  have hlv := (weakNegativeLaplacian_mem_bound hO k hv).1
  have hld := MemWkp.sub (by norm_num : (1:ℝ≥0∞) ≤ 2) hO hlu hlv
  have hqd := memWkp_mul_smooth_of_isCompact_closure k hO hOc (hd.le_of_le (by omega)) hq
  have heq : (fun x => weakFlatOperator O q u x-weakFlatOperator O q v x) =
      fun x => (weakNegativeLaplacian O u x-weakNegativeLaplacian O v x)-q x*(u x-v x) := by
    funext x
    dsimp only [weakFlatOperator]
    ring
  rw [heq]
  calc
    _ ≤ iteratedWeakSobolevNorm k 2 (fun x => weakNegativeLaplacian O u x-weakNegativeLaplacian O v x) O +
        iteratedWeakSobolevNorm k 2 (fun x => q x*(u x-v x)) O := sobolevNorm_sub_le hO hld hqd
    _ ≤ (d:ℝ≥0∞)*iteratedWeakSobolevNorm (k+2) 2 (fun x => u x-v x) O +
        B*iteratedWeakSobolevNorm k 2 (fun x => u x-v x) O :=
      add_le_add (weakNegativeLaplacian_difference_bound hO k hu hv) (hb _ (hd.le_of_le (by omega)))
    _ ≤ (d:ℝ≥0∞)*iteratedWeakSobolevNorm (k+2) 2 (fun x => u x-v x) O +
        B*iteratedWeakSobolevNorm (k+2) 2 (fun x => u x-v x) O :=
      add_le_add le_rfl (mul_le_mul le_rfl (wkpNorm_mono_order (by omega : k ≤ k+2) _ _) zero_le zero_le)
    _ = _ := (add_mul _ _ _).symm

#print axioms sobolevNorm_tendsto_of_difference
#print axioms exists_weakFlatOperator_difference_bound
end Yamabe3.Analysis.UniformElliptic
