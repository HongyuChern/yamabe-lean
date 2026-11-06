import Yamabe3.Analysis.WeakDilationNorm

/-! Uniform full weak Sobolev dilation bounds for a fixed positive compact
range of dilation factors. No continuity of an arbitrarily selected
estimate constant is assumed. -/
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

theorem dilationL2Factor_antitone {a r : ℝ} (ha : 0 < a) (har : a ≤ r) :
    dilationL2Factor d r ≤ dilationL2Factor d a := by
  have hr : 0 < r := ha.trans_le har
  unfold dilationL2Factor
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  apply ENNReal.ofReal_le_ofReal
  rw [abs_of_pos (inv_pos.mpr (pow_pos hr _)),abs_of_pos (inv_pos.mpr (pow_pos ha _))]
  exact inv_anti₀ (pow_pos ha _) (pow_le_pow_left₀ ha.le har _)

theorem exists_uniform_weak_dilation_sobolev_bound (k : ℕ) {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ r : ℝ, a ≤ r → r ≤ b → ∀ (O : Set E), IsOpen O → ∀ u : E → ℝ,
      MemWkp k 2 u O →
      iteratedWeakSobolevNorm k 2 (fun x : E => u (r • x))
        ((fun x : E => r • x) ⁻¹' O) ≤ C * iteratedWeakSobolevNorm k 2 u O := by
  induction k with
  | zero =>
    refine ⟨dilationL2Factor d a,dilationL2Factor_ne_top d a,?_⟩
    intro r har hrb O hO u hu
    have hrpos : 0 < r := ha.trans_le har
    have hr := hrpos.ne'
    have hJ := dilationL2Factor_antitone (d := d) ha har
    have hbr : ENNReal.ofReal |r| ≤ ENNReal.ofReal b := by
      rw [abs_of_pos hrpos]
      exact ENNReal.ofReal_le_ofReal hrb
    simp only [wkpNorm_zero,eLpNorm_comp_dilation hr]
    exact mul_le_mul_of_nonneg_right hJ zero_le
  | succ k ih =>
    obtain ⟨C,hC,hb⟩ := ih
    let D := dilationL2Factor d a + ∑ _i : Fin d, ENNReal.ofReal b*C
    refine ⟨D,ENNReal.add_ne_top.mpr ⟨dilationL2Factor_ne_top d a,
      ENNReal.sum_ne_top.mpr (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC)⟩,?_⟩
    intro r har hrb O hO u hu
    have hrpos : 0 < r := ha.trans_le har
    have hr := hrpos.ne'
    have hJ := dilationL2Factor_antitone (d := d) ha har
    have hbr : ENNReal.ofReal |r| ≤ ENNReal.ofReal b := by
      rw [abs_of_pos hrpos]
      exact ENNReal.ofReal_le_ofReal hrb
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
        (ENNReal.ofReal b*C)*iteratedWeakSobolevNorm (k+1) 2 u O := by
      rw [show g i = fun x => r * chosenWeakPartial' 2 i u O (r • x) from rfl,
        wkpNorm_const_smul hp hW (memWkp_comp_dilation hr hO hp k (hu.chosenWeakPartial_mem i)),
        Real.enorm_eq_ofReal_abs]
      calc
        _ ≤ ENNReal.ofReal |r| * (C*iteratedWeakSobolevNorm k 2 (chosenWeakPartial' 2 i u O) O) :=
          mul_le_mul le_rfl (hb r har hrb O hO _ (hu.chosenWeakPartial_mem i)) zero_le zero_le
        _ ≤ ENNReal.ofReal |r| * (C*iteratedWeakSobolevNorm (k+1) 2 u O) :=
          mul_le_mul le_rfl (mul_le_mul le_rfl
            (wkpNorm_chosenWeakPartial_le_wkpNorm_succ k 2 u O i) zero_le zero_le) zero_le zero_le
        _ ≤ ENNReal.ofReal b * (C*iteratedWeakSobolevNorm (k+1) 2 u O) :=
          mul_le_mul hbr le_rfl zero_le zero_le
        _ = _ := by ring
    rw [wkpNorm_succ_eq k]
    calc
      _ ≤ dilationL2Factor d a * iteratedWeakSobolevNorm (k+1) 2 u O +
          ∑ i : Fin d, (ENNReal.ofReal b*C)*iteratedWeakSobolevNorm (k+1) 2 u O := by
        apply add_le_add
        · rw [eLpNorm_comp_dilation hr]
          exact mul_le_mul hJ (by
            rw [← wkpNorm_zero]
            exact wkpNorm_mono_order (Nat.zero_le _) u O) zero_le zero_le
        · apply Finset.sum_le_sum
          intro i _
          rw [wkpNorm_congr_ae (k := k) hp hW (heq i)]
          exact hgn i
      _ = _ := by dsimp only [D]; rw [add_mul,Finset.sum_mul]


#print axioms exists_uniform_weak_dilation_sobolev_bound
end Yamabe3.Analysis.UniformElliptic
