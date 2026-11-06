import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Weak.PartialLimit
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Actual limits of Cauchy weak Sobolev jets

Every L2 limit is constructed by completeness. The pinned closed weak-
derivative graph theorem then identifies all those limits as the actual
chosen weak derivatives of one and the same function. No higher weak jet
or Sobolev representative is supplied as a conclusion-shaped hypothesis.
This is the local unweighted completion step; the weighted operator
extension and its geometric canonical identity are separate consumers.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Sobolev.Euclidean

/-- Construct the genuine L2 limit from a concrete two-index eLpNorm
Cauchy condition. The representative and its L2 convergence are outputs. -/
theorem exists_memLp_two_limit_of_eLpNorm_cauchy
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} (hf : ∀ n, MemLp (f n) 2 μ)
    (hC : Tendsto (fun nm : ℕ × ℕ => eLpNorm (fun x => f nm.1 x - f nm.2 x) 2 μ)
      atTop (𝓝 0)) :
    ∃ F : α → ℝ, MemLp F 2 μ ∧
      Tendsto (fun n => eLpNorm (fun x => f n x - F x) 2 μ) atTop (𝓝 0) := by
  let z : ℕ → Lp ℝ 2 μ := fun n => (hf n).toLp (f n)
  have hzC : CauchySeq z := by
    apply (Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm z).mpr
    apply hC.congr'
    exact Eventually.of_forall fun nm => by
      apply eLpNorm_congr_ae
      filter_upwards [(hf nm.1).coeFn_toLp, (hf nm.2).coeFn_toLp] with x h₀ h₁
      change f nm.1 x - f nm.2 x = (z nm.1 : α → ℝ) x - (z nm.2 : α → ℝ) x
      rw [show (z nm.1 : α → ℝ) x = f nm.1 x from h₀,
        show (z nm.2 : α → ℝ) x = f nm.2 x from h₁]
  obtain ⟨Z, hZ⟩ := cauchySeq_tendsto_of_complete hzC
  refine ⟨(Z : α → ℝ), Lp.memLp Z, ?_⟩
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' z Z).mp hZ
  apply ht.congr'
  exact Eventually.of_forall fun n => by
    apply eLpNorm_congr_ae
    filter_upwards [(hf n).coeFn_toLp] with x hx
    change (z n : α → ℝ) x - (Z : α → ℝ) x = f n x - (Z : α → ℝ) x
    rw [show (z n : α → ℝ) x = f n x from hx]

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Cauchy of every actual weak jet through k constructs one Hk function.
The convergence statements use its actual weak derivatives, not separately
chosen limits that are silently identified. -/
theorem exists_memWk2_limit_of_iterated_weak_cauchy
    {Ω : Set E} (hΩ : IsOpen Ω) (k : ℕ) {u : ℕ → E → ℝ}
    (hu : ∀ n, MemWkp k 2 (u n) Ω)
    (hC : ∀ (j : ℕ) (β : Fin j → Fin d), j ≤ k →
      Tendsto (fun nm : ℕ × ℕ => eLpNorm
        (fun x => iterWeakPartial 2 j β (u nm.1) Ω x - iterWeakPartial 2 j β (u nm.2) Ω x)
        2 (volume.restrict Ω)) atTop (𝓝 0)) :
    ∃ U : E → ℝ, MemWkp k 2 U Ω ∧
      ∀ (j : ℕ) (β : Fin j → Fin d), j ≤ k →
        Tendsto (fun n => eLpNorm
          (fun x => iterWeakPartial 2 j β (u n) Ω x - iterWeakPartial 2 j β U Ω x)
          2 (volume.restrict Ω)) atTop (𝓝 0) := by
  classical
  have hlim (j : ℕ) (β : Fin j → Fin d) (hj : j ≤ k) :
      ∃ V : E → ℝ, MemLp V 2 (volume.restrict Ω) ∧
        Tendsto (fun n => eLpNorm
          (fun x => iterWeakPartial 2 j β (u n) Ω x - V x)
          2 (volume.restrict Ω)) atTop (𝓝 0) :=
    exists_memLp_two_limit_of_eLpNorm_cauchy
      (fun n => iterWeakPartial_memLp_of_memWkp ((hu n).le_of_le hj) β)
      (hC j β hj)
  choose V hV hT using hlim
  let v : ∀ j : ℕ, (Fin j → Fin d) → E → ℝ :=
    fun j β => if hj : j ≤ k then V j β hj else 0
  have hv (j : ℕ) (β : Fin j → Fin d) (hj : j ≤ k) :
      MemLp (v j β) 2 (volume.restrict Ω) := by
    simpa only [v, dif_pos hj] using hV j β hj
  have ht (j : ℕ) (β : Fin j → Fin d) (hj : j ≤ k) :
      Tendsto (fun n => eLpNorm
        (fun x => iterWeakPartial 2 j β (u n) Ω x - v j β x)
        2 (volume.restrict Ω)) atTop (𝓝 0) := by
    simpa only [v, dif_pos hj] using hT j β hj
  obtain ⟨hU, hjet⟩ := MemWkp_of_iter_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hΩ k hu v hv ht
  refine ⟨v 0 ![], hU, ?_⟩
  intro j β hj
  apply (ht j β hj).congr'
  exact Eventually.of_forall fun n => by
    apply eLpNorm_congr_ae
    filter_upwards [hjet j β hj] with x hx
    rw [hx]

/-- The constructed Sobolev limit is unique as an actual L2 function
class whenever another representative is an L2 limit of the same values. -/
theorem ae_eq_of_two_memLp_value_limits
    {Ω : Set E} {u : ℕ → E → ℝ} {U V : E → ℝ}
    (hu : ∀ n, MemLp (u n) 2 (volume.restrict Ω))
    (hU : MemLp U 2 (volume.restrict Ω)) (hV : MemLp V 2 (volume.restrict Ω))
    (huU : Tendsto (fun n => eLpNorm (fun x => u n x - U x) 2 (volume.restrict Ω)) atTop (𝓝 0))
    (huV : Tendsto (fun n => eLpNorm (fun x => u n x - V x) 2 (volume.restrict Ω)) atTop (𝓝 0)) :
    U =ᵐ[volume.restrict Ω] V := by
  have htU := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' u hu U hU).mpr huU
  have htV := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' u hu V hV).mpr huV
  have heq := tendsto_nhds_unique htU htV
  have hcoe : (hU.toLp U : E → ℝ) =ᵐ[volume.restrict Ω] (hV.toLp V : E → ℝ) := by
    rw [heq]
  exact hU.coeFn_toLp.symm.trans (hcoe.trans hV.coeFn_toLp)

#print axioms exists_memLp_two_limit_of_eLpNorm_cauchy
#print axioms exists_memWk2_limit_of_iterated_weak_cauchy
#print axioms ae_eq_of_two_memLp_value_limits

end Yamabe3.Analysis.UniformElliptic
