import Yamabe3.Analysis.NativeWeakDilation
import Yamabe3.Analysis.BoundaryH2SobolevEstimate

/-! The genuine weak full Sobolev norm under a fixed physical dilation,
including its three-dimensional (or d-dimensional) volume factor. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ENNReal ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

def dilationL2Factor (d : ℕ) (r : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal |(r ^ d)⁻¹|) ^ (1 / (2 : ℝ≥0∞)).toReal

theorem dilationL2Factor_ne_top (d : ℕ) (r : ℝ) : dilationL2Factor d r ≠ ⊤ := by
  unfold dilationL2Factor
  apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
  exact ENNReal.ofReal_ne_top

theorem eLpNorm_comp_dilation {r : ℝ} (hr : r ≠ 0) (O : Set E) (u : E → ℝ) :
    eLpNorm (fun x : E => u (r • x)) 2 (volume.restrict ((fun x : E => r • x) ⁻¹' O)) =
      dilationL2Factor d r * eLpNorm u 2 (volume.restrict O) := by
  have he : MeasurableEmbedding (fun x : E => r • x) :=
    (Homeomorph.smulOfNeZero r hr : E ≃ₜ E).measurableEmbedding
  change eLpNorm (u ∘ (fun x : E => r • x)) 2 _ = _
  rw [← he.eLpNorm_map_measure,map_restrict_volume_dilation hr,
    eLpNorm_smul_measure_of_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr
      (abs_pos.mpr (inv_ne_zero (pow_ne_zero _ hr)))))]
  simp only [finrank_euclideanSpace, Fintype.card_fin, dilationL2Factor, smul_eq_mul]

theorem exists_weak_dilation_sobolev_bound (k : ℕ) {r : ℝ} (hr : r ≠ 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (O : Set E), IsOpen O → ∀ u : E → ℝ,
      MemWkp k 2 u O →
      iteratedWeakSobolevNorm k 2 (fun x : E => u (r • x))
        ((fun x : E => r • x) ⁻¹' O) ≤ C * iteratedWeakSobolevNorm k 2 u O := by
  induction k with
  | zero =>
    refine ⟨dilationL2Factor d r,dilationL2Factor_ne_top d r,?_⟩
    intro O hO u hu
    simp only [wkpNorm_zero,eLpNorm_comp_dilation hr]
    exact le_rfl
  | succ k ih =>
    obtain ⟨C,hC,hb⟩ := ih
    let D := dilationL2Factor d r + ∑ _i : Fin d, ENNReal.ofReal |r| *C
    refine ⟨D,ENNReal.add_ne_top.mpr ⟨dilationL2Factor_ne_top d r,
      ENNReal.sum_ne_top.mpr (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC)⟩,?_⟩
    intro O hO u hu
    let W := (fun x : E => r • x) ⁻¹' O
    have hW : IsOpen W := hO.preimage (continuous_id.const_smul r)
    have hp : (1:ℝ≥0∞) ≤ 2 := by norm_num
    have hcomp := memWkp_comp_dilation hr hO hp (k+1) hu
    let g (i : Fin d) (x : E) := r * chosenWeakPartial' 2 i u O (r • x)
    have hg (i : Fin d) : MemWkp k 2 (g i) W :=
      MemWkp.const_smul hp hW (memWkp_comp_dilation hr hO hp k (hu.chosenWeakPartial_mem i)) r
    have heq (i : Fin d) : chosenWeakPartial' 2 i (fun x : E => u (r • x)) W =ᵐ[volume.restrict W] g i :=
      HasWeakPartialDeriv.ae_eq hW
        (chosenWeakPartial'_isWeakPartial_of_mem hcomp.memW1p i)
        (hasWeakPartialDeriv_comp_dilation hr (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i))
        ((chosenWeakPartial'_memLp_of_mem hcomp.memW1p i).locallyIntegrable hp)
        ((hg i).memLp.locallyIntegrable hp)
    have hgn (i : Fin d) : iteratedWeakSobolevNorm k 2 (g i) W ≤
        (ENNReal.ofReal |r| *C)*iteratedWeakSobolevNorm (k+1) 2 u O := by
      rw [show g i = fun x => r * chosenWeakPartial' 2 i u O (r • x) from rfl,
        wkpNorm_const_smul hp hW (memWkp_comp_dilation hr hO hp k (hu.chosenWeakPartial_mem i)),
        Real.enorm_eq_ofReal_abs]
      calc
        _ ≤ ENNReal.ofReal |r| * (C*iteratedWeakSobolevNorm k 2 (chosenWeakPartial' 2 i u O) O) :=
          mul_le_mul le_rfl (hb O hO _ (hu.chosenWeakPartial_mem i)) zero_le zero_le
        _ ≤ ENNReal.ofReal |r| * (C*iteratedWeakSobolevNorm (k+1) 2 u O) :=
          mul_le_mul le_rfl (mul_le_mul le_rfl
            (wkpNorm_chosenWeakPartial_le_wkpNorm_succ k 2 u O i) zero_le zero_le) zero_le zero_le
        _ = _ := by ring
    rw [wkpNorm_succ_eq k]
    calc
      _ ≤ dilationL2Factor d r * iteratedWeakSobolevNorm (k+1) 2 u O +
          ∑ i : Fin d, (ENNReal.ofReal |r| *C)*iteratedWeakSobolevNorm (k+1) 2 u O := by
        apply add_le_add
        · rw [eLpNorm_comp_dilation hr]
          exact mul_le_mul le_rfl (by
            rw [← wkpNorm_zero]
            exact wkpNorm_mono_order (Nat.zero_le _) u O) zero_le zero_le
        · apply Finset.sum_le_sum
          intro i _
          rw [wkpNorm_congr_ae (k := k) hp hW (heq i)]
          exact hgn i
      _ = _ := by dsimp only [D]; rw [add_mul,Finset.sum_mul]

#print axioms eLpNorm_comp_dilation
#print axioms exists_weak_dilation_sobolev_bound
end Yamabe3.Analysis.UniformElliptic
