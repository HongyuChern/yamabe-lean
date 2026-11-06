import Yamabe3.Analysis.NativeFullWeightedH4

/-! On the original basic annulus, the same weighted half-end field has
one H4 bound for every s >= 4. This is the tail of the full graph bound;
the finite entrance interval is treated by the separate real collar. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_uniform_full_weighted_tail_H4_bound
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (p : DelaunayPhaseData κ) (f : HalfEndPhysicalH2SourceGraph) (s : ℝ),
      4 ≤ s → MemWkp 4 2 (actualWeightedFullModelField hκ0 hκ1 p f s) halfEndBasicAnnulus ∧
        iteratedWeakSobolevNorm 4 2 (actualWeightedFullModelField hκ0 hκ1 p f s) halfEndBasicAnnulus ≤
          C*ENNReal.ofReal ‖f‖ := by
  have hlog : Real.log 2 < 2 := lt_of_le_of_lt (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)) (by norm_num)
  have heq : cylinderAnnulus (-Real.log 2) (Real.log 2) = halfEndBasicAnnulus := by
    ext x
    simp only [cylinderAnnulus,halfEndBasicAnnulus,mem_setOf_eq,neg_neg,
      Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ) < 2)]
    norm_num
  obtain ⟨C,hC,hb⟩ := exists_uniform_full_weighted_H4_bound hκ0 hκ1
    (isOpen_cylinderAnnulus (-3) 3) (isCompact_closure_cylinderAnnulus (-3) 3)
    (fun x hx => cylinderShell_ne_zero (closure_cylinderAnnulus_subset_shell (-3) 3 hx))
    (R := Real.exp 3) (Real.one_le_exp_iff.mpr (by norm_num))
    (fun x hx => by simpa only [neg_neg] using (closure_cylinderAnnulus_subset_shell (-3) 3 hx).2)
    (isOpen_cylinderAnnulus (-2) 2) (isCompact_closure_cylinderAnnulus (-2) 2)
    (closure_cylinderAnnulus_subset_wider (by norm_num : (-3:ℝ) < -2) (by norm_num : (2:ℝ) < 3))
    (isOpen_cylinderAnnulus (-Real.log 2) (Real.log 2))
    (isCompact_closure_cylinderAnnulus (-Real.log 2) (Real.log 2))
    (closure_cylinderAnnulus_subset_wider (by linarith : (-2:ℝ) < -Real.log 2) hlog)
    (-2) 2 (cylinderAnnulus_subset_shell (-2) 2)
  refine ⟨C,hC,?_⟩
  intro p f s hs
  simpa only [heq,Real.log_exp] using hb p f s (by simpa only [Real.log_exp,show (3:ℝ)+1=4 by norm_num] using hs)

#print axioms exists_uniform_full_weighted_tail_H4_bound
end Yamabe3.Analysis.UniformElliptic
