import Yamabe3.Analysis.NativeScaledCollarEnergy
import Yamabe3.Analysis.NativeCollarDyadicPartition
import Mathlib.Analysis.SpecificLimits.Normed

/-! An actual operator-norm convergent energy series over shrinking
collars. Uniform weighted jets pay exp(-n/2), and all summands use the
same input. Physical value identification is a separate proved gate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD
variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ) (hs:tsupport χ⊆nativePoissonEntranceCollar)
  (J:ℕ→X →L[ℝ] nativeCollarJetClosure)

def nativeInnerEnergySeriesPiece (n:ℕ):X →L[ℝ] H1Zero Deuc univ :=
  (nativeScaledCollarEnergyCLM χ hχ hc hs (((n+1:ℕ):ℝ)/4) (by positivity)).comp (J n)

theorem nativeInnerEnergySeriesPiece_bound {C:ℝ} (hC:0 ≤ C) (hJ:∀n:ℕ,‖J n‖ ≤ C) (n:ℕ) :
    ‖nativeInnerEnergySeriesPiece χ hχ hc hs J n‖ ≤
      (2*‖nativeCollarCutoffRawCLM χ hχ‖*C)*(Real.exp (-(1/2:ℝ)))^n := by
  have hh:=ContinuousLinearMap.opNorm_comp_le
    (nativeScaledCollarEnergyCLM χ hχ hc hs (((n+1:ℕ):ℝ)/4) (by positivity)) (J n)
  have hE:=nativeScaledCollarEnergyCLM_norm χ hχ hc hs (((n+1:ℕ):ℝ)/4) (by positivity)
  have he:(Real.exp (-(1/2:ℝ)))^n=Real.exp (-(n:ℝ)/2) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  apply (hh.trans (mul_le_mul hE (hJ n) (norm_nonneg _) (by positivity))).trans
  have hs': -2*(((n+1:ℕ):ℝ)/4) ≤ -(n:ℝ)/2 := by push_cast;linarith
  calc
    _=(2*‖nativeCollarCutoffRawCLM χ hχ‖*C)*Real.exp (-2*(((n+1:ℕ):ℝ)/4)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs') (by positivity)

theorem nativeInnerEnergySeries_summable_norm {C:ℝ} (hC:0 ≤ C) (hJ:∀n:ℕ,‖J n‖ ≤ C) :
    Summable (fun n:ℕ=>‖nativeInnerEnergySeriesPiece χ hχ hc hs J n‖) := by
  have hg:Summable (fun n:ℕ=>(2*‖nativeCollarCutoffRawCLM χ hχ‖*C)*(Real.exp (-(1/2:ℝ)))^n) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by norm_num))).mul_left _
  exact Summable.of_nonneg_of_le (fun n=>norm_nonneg (nativeInnerEnergySeriesPiece χ hχ hc hs J n))
    (fun n=>nativeInnerEnergySeriesPiece_bound χ hχ hc hs J hC hJ n) hg

theorem nativeInnerEnergySeries_summable {C:ℝ} (hC:0 ≤ C) (hJ:∀n:ℕ,‖J n‖ ≤ C) :
    Summable (nativeInnerEnergySeriesPiece χ hχ hc hs J) :=
  Summable.of_norm (f:=nativeInnerEnergySeriesPiece χ hχ hc hs J)
    (nativeInnerEnergySeries_summable_norm χ hχ hc hs J hC hJ)

def nativeInnerEnergySeriesCLM : X →L[ℝ] H1Zero Deuc univ :=
  ∑'n:ℕ,nativeInnerEnergySeriesPiece χ hχ hc hs J n

theorem nativeInnerEnergySeriesCLM_norm {C:ℝ} (hC:0 ≤ C) (hJ:∀n:ℕ,‖J n‖ ≤ C) :
    ‖nativeInnerEnergySeriesCLM χ hχ hc hs J‖ ≤
      (2*‖nativeCollarCutoffRawCLM χ hχ‖*C)/(1-Real.exp (-(1/2:ℝ))) := by
  have hg:Summable (fun n:ℕ=>(2*‖nativeCollarCutoffRawCLM χ hχ‖*C)*(Real.exp (-(1/2:ℝ)))^n) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by norm_num))).mul_left _
  change ‖∑'n:ℕ,nativeInnerEnergySeriesPiece χ hχ hc hs J n‖ ≤ _
  apply (norm_tsum_le_tsum_norm (f:=nativeInnerEnergySeriesPiece χ hχ hc hs J)
    (nativeInnerEnergySeries_summable_norm χ hχ hc hs J hC hJ)).trans
  apply ((nativeInnerEnergySeries_summable_norm χ hχ hc hs J hC hJ).tsum_le_tsum
    (nativeInnerEnergySeriesPiece_bound χ hχ hc hs J hC hJ) hg).trans_eq
  rw [tsum_mul_left,tsum_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by norm_num))]
  simp only [div_eq_mul_inv]

theorem nativeInnerEnergySeries_partial_tendsto {C:ℝ} (hC:0 ≤ C) (hJ:∀n:ℕ,‖J n‖ ≤ C) (x:X) :
    Tendsto (fun N:ℕ=>∑n∈Finset.range N,nativeInnerEnergySeriesPiece χ hχ hc hs J n x)
      atTop (𝓝 (nativeInnerEnergySeriesCLM χ hχ hc hs J x)) := by
  let ev:=ContinuousLinearMap.apply ℝ (H1Zero Deuc univ) x
  exact (ev.hasSum (nativeInnerEnergySeries_summable χ hχ hc hs J hC hJ).hasSum).tendsto_sum_nat

#print axioms nativeInnerEnergySeriesPiece_bound
#print axioms nativeInnerEnergySeries_summable
#print axioms nativeInnerEnergySeriesCLM_norm
#print axioms nativeInnerEnergySeries_partial_tendsto
end Yamabe3.Analysis.SpherePolar
