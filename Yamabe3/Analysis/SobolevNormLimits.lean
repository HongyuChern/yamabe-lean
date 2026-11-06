import Yamabe3.Analysis.UniformElliptic.WeakSobolevCauchyLimit
import Yamabe3.Analysis.BoundaryLocalizedSourceBound

/-! Closed weak jets and convergence of the full (finite sum) Sobolev norm. -/
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

theorem iterWeakPartial_sub_two_ae {O : Set E} (hO : IsOpen O)
    {j : ℕ} (β : Fin j → Fin d) {u v : E → ℝ}
    (hu : MemWkp j 2 u O) (hv : MemWkp j 2 v O) :
    iterWeakPartial 2 j β (fun x => u x - v x) O =ᵐ[volume.restrict O]
      fun x => iterWeakPartial 2 j β u O x - iterWeakPartial 2 j β v O x := by
  have ha := iterWeakPartial_add_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2) hO β hu
    (MemWkp.const_smul (by norm_num) hO hv (-1))
  have hn := iterWeakPartial_const_smul_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2) hO β hv (-1)
  simp only [neg_one_mul] at ha hn
  filter_upwards [ha, hn] with x hx hn
  simpa only [← sub_eq_add_neg, hn] using hx

theorem jet_eLpNorm_le_sobolevNorm (k j : ℕ) (hj : j ≤ k)
    (β : Fin j → Fin d) (u : E → ℝ) (O : Set E) :
    eLpNorm (iterWeakPartial 2 j β u O) 2 (volume.restrict O) ≤
      iteratedWeakSobolevNorm k 2 u O := by
  classical
  exact (Finset.single_le_sum (f := fun β : Fin j → Fin d =>
    eLpNorm (iterWeakPartial 2 j β u O) 2 (volume.restrict O)) (fun _ _ => zero_le) (Finset.mem_univ β)).trans
    (Finset.single_le_sum (f := fun j => ∑ β : Fin j → Fin d,
      eLpNorm (iterWeakPartial 2 j β u O) 2 (volume.restrict O))
      (fun _ _ => zero_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

theorem jet_difference_le_sobolev_difference {O : Set E} (hO : IsOpen O)
    {k j : ℕ} (hj : j ≤ k) (β : Fin j → Fin d) {u v : E → ℝ}
    (hu : MemWkp k 2 u O) (hv : MemWkp k 2 v O) :
    eLpNorm (fun x => iterWeakPartial 2 j β u O x - iterWeakPartial 2 j β v O x)
      2 (volume.restrict O) ≤ iteratedWeakSobolevNorm k 2 (fun x => u x - v x) O := by
  rw [← eLpNorm_congr_ae (iterWeakPartial_sub_two_ae hO β (hu.le_of_le hj) (hv.le_of_le hj))]
  exact jet_eLpNorm_le_sobolevNorm k j hj β _ O

theorem eLpNorm_tendsto_of_L2_difference {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hF : MemLp F 2 μ)
    (ht : Tendsto (fun n => eLpNorm (fun x => f n x - F x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 (eLpNorm F 2 μ)) := by
  have hh := ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf F hF).mpr ht).enorm
  simpa only [Lp.enorm_toLp] using hh

theorem sobolevNorm_tendsto_of_jet_limits {O : Set E} {k : ℕ}
    {u : ℕ → E → ℝ} {U : E → ℝ}
    (hu : ∀ n, MemWkp k 2 (u n) O) (hU : MemWkp k 2 U O)
    (ht : ∀ j (β : Fin j → Fin d), j ≤ k →
      Tendsto (fun n => eLpNorm (fun x => iterWeakPartial 2 j β (u n) O x -
        iterWeakPartial 2 j β U O x) 2 (volume.restrict O)) atTop (𝓝 0)) :
    Tendsto (fun n => iteratedWeakSobolevNorm k 2 (u n) O) atTop
      (𝓝 (iteratedWeakSobolevNorm k 2 U O)) := by
  classical
  unfold iteratedWeakSobolevNorm
  apply tendsto_finset_sum
  intro j hj
  apply tendsto_finset_sum
  intro β _
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  exact eLpNorm_tendsto_of_L2_difference
    (fun n => iterWeakPartial_memLp_of_memWkp ((hu n).le_of_le hjk) β)
    (iterWeakPartial_memLp_of_memWkp (hU.le_of_le hjk) β) (ht j β hjk)

/-- Cauchy in the full actual norm constructs one weak Sobolev limit,
with all jets and the full norm converging. -/
theorem exists_sobolev_limit_of_norm_cauchy {O : Set E} (hO : IsOpen O) (k : ℕ)
    {u : ℕ → E → ℝ} (hu : ∀ n, MemWkp k 2 (u n) O)
    (hC : Tendsto (fun nm : ℕ × ℕ => iteratedWeakSobolevNorm k 2
      (fun x => u nm.1 x - u nm.2 x) O) atTop (𝓝 0)) :
    ∃ U : E → ℝ, MemWkp k 2 U O ∧
      (∀ j (β : Fin j → Fin d), j ≤ k →
        Tendsto (fun n => eLpNorm (fun x => iterWeakPartial 2 j β (u n) O x -
          iterWeakPartial 2 j β U O x) 2 (volume.restrict O)) atTop (𝓝 0)) ∧
      Tendsto (fun n => iteratedWeakSobolevNorm k 2 (u n) O) atTop
        (𝓝 (iteratedWeakSobolevNorm k 2 U O)) := by
  obtain ⟨U, hU, ht⟩ := exists_memWk2_limit_of_iterated_weak_cauchy hO k hu
    (fun j β hj => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hC
      (fun _ => zero_le)
      (fun nm : ℕ × ℕ => jet_difference_le_sobolev_difference hO hj β (hu nm.1) (hu nm.2)))
  exact ⟨U, hU, ht, sobolevNorm_tendsto_of_jet_limits hu hU ht⟩

#print axioms iterWeakPartial_sub_two_ae
#print axioms exists_sobolev_limit_of_norm_cauchy
end Yamabe3.Analysis.UniformElliptic
