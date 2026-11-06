import Yamabe3.Analysis.NativeFullUnweightedH4
import Yamabe3.Analysis.NativeFullPhysicalCollar

/-! Uniform local physical H4 bounds for the same full-source physical field,
inside the punctured unit ball, before the orbit, phase and source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "O" => ball (0:E) 1 \ {(0:E)}

theorem exists_uniform_full_model_local_H4_bound
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) {a : E} (ha : a ∈ O) :
    ∃ (W : Set E) (C : ℝ≥0∞), a ∈ W ∧ IsOpen W ∧ W ⊆ O ∧ C ≠ ⊤ ∧
      ∀ (p : DelaunayPhaseData κ) (f : HalfEndPhysicalH2SourceGraph),
        MemWkp 4 2 (fullModelPhysicalField hκ0 hκ1 p f) W ∧
        iteratedWeakSobolevNorm 4 2 (fullModelPhysicalField hκ0 hκ1 p f) W ≤ C*ENNReal.ofReal ‖f‖ := by
  have ha0 : a ≠ 0 := by simpa only [mem_singleton_iff] using ha.2
  have han : ‖a‖ < 1 := by simpa only [mem_ball,dist_zero_right] using ha.1
  let t := -Real.log ‖a‖
  have ht : 0 < t := neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr ha0) han)
  let N := cylinderAnnulus (t/4) (t+3)
  let V := cylinderAnnulus (t/2) (t+2)
  let W := cylinderAnnulus (3*t/4) (t+1)
  have hNc : IsCompact (closure N) := isCompact_closure_cylinderAnnulus _ _
  have hNO : closure N ⊆ O := by
    intro x hx
    have hs := closure_cylinderAnnulus_subset_shell (t/4) (t+3) hx
    refine ⟨?_,?_⟩
    · simpa only [mem_ball,dist_zero_right] using hs.2.trans_lt (Real.exp_lt_one_iff.mpr (by linarith))
    · exact cylinderShell_ne_zero hs
  have hVN : closure V ⊆ N := closure_cylinderAnnulus_subset_wider (by linarith) (by linarith)
  have hWV : closure W ⊆ V := closure_cylinderAnnulus_subset_wider (by linarith) (by linarith)
  have hWO : W ⊆ O := fun x hx => hNO (subset_closure (hVN (subset_closure (hWV (subset_closure hx)))))
  obtain ⟨C,hC,hb⟩ := exists_uniform_full_unweighted_H4_bound hκ0 hκ1
    (isOpen_cylinderAnnulus _ _) hNc hNO (isOpen_cylinderAnnulus _ _)
    (isCompact_closure_cylinderAnnulus _ _) hVN (isOpen_cylinderAnnulus _ _)
    (isCompact_closure_cylinderAnnulus _ _) hWV (t/2) (t+2) (cylinderAnnulus_subset_shell _ _)
  have hW : IsOpen W := isOpen_cylinderAnnulus _ _
  refine ⟨W,C,mem_cylinderAnnulus_of_log_norm ha0 (by dsimp only [t]; linarith) (by dsimp only [t]; linarith),hW,hWO,hC,?_⟩
  intro p f
  have he:actualWeightedFullModelField hκ0 hκ1 p f 0=fullModelPhysicalField hκ0 hκ1 p f:=by
    funext x
    simp only [actualWeightedFullModelField,mul_zero,zero_div,Real.exp_zero,neg_zero,one_smul,one_mul]
  have hh:=hb p f
  rw [he] at hh
  exact hh

#print axioms exists_uniform_full_model_local_H4_bound
end Yamabe3.Analysis.UniformElliptic
