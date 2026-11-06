import Yamabe3.Analysis.NativeUnweightedInteriorH4
import Yamabe3.Analysis.NativeDelaunayUniformCollar

/-! Uniform local physical H4 bounds for the one canonical completion,
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

theorem exists_uniform_completion_local_H4_bound
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) {a : E} (ha : a ∈ O) :
    ∃ (W : Set E) (C : ℝ≥0∞), a ∈ W ∧ IsOpen W ∧ W ⊆ O ∧ C ≠ ⊤ ∧
      ∀ (p : DelaunayPhaseData κ) (f : HalfEndHighH2Source),
        MemWkp 4 2 (toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f)) W ∧
        iteratedWeakSobolevNorm 4 2 (toL2 nativeWeakEuclideanD O
          (delaunayPhaseCompletion hκ0 hκ1 p f)) W ≤ C*ENNReal.ofReal ‖f.1‖ := by
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
  obtain ⟨C,hC,hb⟩ := exists_uniform_unweighted_interior_H4_bound hκ0 hκ1
    (isOpen_cylinderAnnulus _ _) hNc hNO (isOpen_cylinderAnnulus _ _)
    (isCompact_closure_cylinderAnnulus _ _) hVN (isOpen_cylinderAnnulus _ _)
    (isCompact_closure_cylinderAnnulus _ _) hWV (t/2) (t+2) (cylinderAnnulus_subset_shell _ _)
  have hW : IsOpen W := isOpen_cylinderAnnulus _ _
  refine ⟨W,C,mem_cylinderAnnulus_of_log_norm ha0 (by dsimp only [t]; linarith) (by dsimp only [t]; linarith),hW,hWO,hC,?_⟩
  intro p f
  have he : (toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f) : E → ℝ) =ᵐ[volume.restrict W]
      actualWeightedHalfEndField hκ0 hκ1 p f 0 := by
    filter_upwards [ae_restrict_mem hW.measurableSet,
      ae_restrict_of_ae (nativeHalfEndH2SourceCompletion_rep hκ0 hκ1 p.potential
        p.kernel_bound p.potential_nonneg p.potential_smooth f)] with x hx hr
    change _ = _ at hr
    have h := hr.trans (indicator_of_mem (hWO hx) _)
    simpa only [delaunayPhaseCompletion,actualWeightedHalfEndField,mul_zero,zero_div,Real.exp_zero,neg_zero,one_smul,one_mul]
      using h
  refine ⟨(MemWkp_congr_ae (by norm_num) hW he).mpr (hb p f).1,?_⟩
  rw [wkpNorm_congr_ae (k := 4) (by norm_num) hW he]
  exact (hb p f).2

#print axioms exists_uniform_completion_local_H4_bound
end Yamabe3.Analysis.UniformElliptic
