import Yamabe3.Analysis.NativeHomogeneousSmallReturnComposition
import Yamabe3.Analysis.StrictLinearFeedback

/-! Ordered far cutoff / small physical scale closure. The far Newton
constant is fixed before choosing S. The geometric constant may depend
on that fixed S, and is paid only by the subsequently chosen a. Actual
source/field maps must be constructed separately; no such map is assumed
into the project's main target by this operator lemma. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter
open scoped Topology NNReal
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar

theorem exists_ordered_feedback_far_scale (Ci N Ccut S₀ L:ℝ)
    (hCi:0 ≤ Ci) (hN:0 ≤ N) (hcut:0 ≤ Ccut) (hL:0 < L) :
    ∃S:ℝ,S ≤ S₀ ∧ L ≤ Real.exp (-S-1/2) ∧ Ci*N*Ccut*Real.exp (S/2) ≤ 1/8 := by
  let D:=Ci*N*Ccut
  have hD:0 ≤ D := by dsimp only [D];positivity
  let B:=1+8*D
  have hB:0 < B := by dsimp only [B];positivity
  let S:=min S₀ (min (-2*Real.log B) (-Real.log L-1/2))
  have hS:S ≤ -2*Real.log B := (min_le_right _ _).trans (min_le_left _ _)
  have hSL:S ≤ -Real.log L-1/2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨S,min_le_left _ _,?_,?_⟩
  · exact (Real.exp_log hL).symm.trans_le (Real.exp_le_exp.mpr (by linarith))
  · have hex:Real.exp (S/2) ≤ B⁻¹ := by
      have hh:=Real.exp_le_exp.mpr (show S/2 ≤ -Real.log B by linarith)
      simpa only [Real.exp_neg,Real.exp_log hB] using hh
    change D*Real.exp (S/2) ≤ 1/8
    apply (mul_le_mul_of_nonneg_left hex hD).trans
    rw [←div_eq_mul_inv]
    apply (div_le_iff₀ hB).mpr
    dsimp only [B]
    linarith

theorem exists_ordered_feedback_small_scale (Ci N Cgeo:ℝ)
    (hCi:0 ≤ Ci) (hN:0 ≤ N) (hgeo:0 ≤ Cgeo) :
    ∃δ:ℝ,0 < δ ∧ δ ≤ 1/2 ∧ ∀a:ℝ,0 ≤ a → a ≤ δ → Ci*N*Cgeo*a ≤ 1/8 := by
  let D:=Ci*N*Cgeo
  have hD:0 ≤ D := by dsimp only [D];positivity
  let B:=1+8*D
  have hB:0 < B := by dsimp only [B];positivity
  let δ:=min (1/2:ℝ) (1/(8*B))
  refine ⟨δ,lt_min (by norm_num) (by positivity),min_le_left _ _,fun a ha haδ=>?_⟩
  change D*a ≤ 1/8
  apply (mul_le_mul_of_nonneg_left (haδ.trans (min_le_right _ _)) hD).trans
  have hDB:D ≤ B := by dsimp only [B];linarith
  apply (mul_le_mul_of_nonneg_right hDB (by positivity:0 ≤ 1/(8*B))).trans_eq
  field_simp

variable {X H:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem two_scale_return_comp_norm
    (I:H →L[ℝ] X) (R:X →L[ℝ] H) (Ci N Ccut Cgeo a S:ℝ)
    (hCi:0 ≤ Ci) (hN:0 ≤ N) (ha:0 < a)
    (hI:‖I‖ ≤ Ci*Real.exp (-Real.log a/2))
    (hR:‖R‖ ≤ N*Real.sqrt a*(Ccut*Real.exp (S/2)+Cgeo*a)) :
    ‖I.comp R‖ ≤ Ci*N*(Ccut*Real.exp (S/2)+Cgeo*a) := by
  apply (ContinuousLinearMap.opNorm_comp_le I R).trans
  apply (mul_le_mul hI hR (norm_nonneg R) (by positivity)).trans_eq
  calc
    _=(Ci*N*(Ccut*Real.exp (S/2)+Cgeo*a))*(Real.exp (-Real.log a/2)*Real.sqrt a) := by ring
    _=_ := by rw [exp_negative_half_log_mul_sqrt ha,mul_one]

theorem exists_two_scale_preconditioned_feedback
    (A:X →L[ℝ] X) (I:H →L[ℝ] X) (R:X →L[ℝ] H)
    (Ci N Ccut Cgeo a S:ℝ) (hCi:0 ≤ Ci) (hN:0 ≤ N) (ha:0 < a)
    (hA:‖A‖ ≤ 2) (hI:‖I‖ ≤ Ci*Real.exp (-Real.log a/2))
    (hR:‖R‖ ≤ N*Real.sqrt a*(Ccut*Real.exp (S/2)+Cgeo*a))
    (hfar:Ci*N*Ccut*Real.exp (S/2) ≤ 1/8)
    (hsmall:Ci*N*Cgeo*a ≤ 1/8) :
    ∃T:X →L[ℝ] X,‖T‖ ≤ 4 ∧ ∀f:X,A (f+I (R (T f)))=T f := by
  have hIR:=two_scale_return_comp_norm I R Ci N Ccut Cgeo a S hCi hN ha hI hR
  have hK:‖I.comp R‖ ≤ 1/4 := hIR.trans (by nlinarith)
  have hgap:‖A‖*‖I.comp R‖ ≤ (1/2:ℝ≥0) :=
    (mul_le_mul hA hK (norm_nonneg _) (by norm_num:0 ≤ (2:ℝ))).trans_eq (by norm_num)
  let T:=strictFeedbackCLM A (I.comp R) (q:=(1/2:ℝ≥0)) (by norm_num) hgap
  refine ⟨T,?_,fun f=>strictFeedback_fixed A (I.comp R) (q:=(1/2:ℝ≥0)) (by norm_num) hgap f⟩
  have hb:=strictFeedbackCLM_norm A (I.comp R) (q:=(1/2:ℝ≥0)) (by norm_num) hgap
  change ‖T‖ ≤ _ at hb
  exact hb.trans ((div_le_div_of_nonneg_right hA (by norm_num)).trans_eq (by norm_num))

#print axioms exists_ordered_feedback_far_scale
#print axioms exists_ordered_feedback_small_scale
#print axioms two_scale_return_comp_norm
#print axioms exists_two_scale_preconditioned_feedback
end Yamabe3.Analysis.UniformElliptic
