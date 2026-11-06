import Yamabe3.Analysis.WeightedH4RepresentativeTransport

/-! The retained continuous value-coordinate norm is proved, not dropped
from the graph norm. The weighted decay controls the inner ball, and one
fixed compact-annulus embedding controls the rest of the entrance ball. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric
open scoped ENNReal ContDiff Topology BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_weighted_H4_entrance_value_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : E → ℝ), Continuous F → F 0 = 0 →
      ∀ B A : ℝ≥0∞, B ≠ ⊤ → A ≠ ⊤ →
      (∀ s : ℝ, -Real.log 2 ≤ s → MemWkp 4 2 (weightedPhysicalDilation s F) halfEndBasicAnnulus ∧
        iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s F) halfEndBasicAnnulus ≤ B) →
      MemWkp 4 2 F (cylinderAnnulus (-5) 6) →
      iteratedWeakSobolevNorm 4 2 F (cylinderAnnulus (-5) 6) ≤ A →
      ∀ x ∈ closedBall (0:E) 4, ‖F x‖ ≤ D*(B.toReal+A.toReal) := by
  let K : Set E := closedBall (0:E) 4 \ ball (0:E) 1
  have hK : IsCompact K := (isCompact_closedBall (0:E) 4).diff isOpen_ball
  have hKV : K ⊆ cylinderAnnulus (-5) 6 := by
    intro x hx
    have hnlo : 1 ≤ ‖x‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hx.2
    have hnhi : ‖x‖ ≤ 4 := by simpa only [mem_closedBall,dist_zero_right] using hx.1
    refine ⟨(Real.exp_lt_one_iff.mpr (by norm_num)).trans_le hnlo,?_⟩
    have hh := Real.add_one_le_exp (5:ℝ)
    simp only [neg_neg]
    linarith
  obtain ⟨C,hC,hc⟩ := exists_weak_H4_sup_bound_on_compact hK (isOpen_cylinderAnnulus (-5) 6) hKV
  obtain ⟨D,hD,hd⟩ := exists_weighted_H4_decay_constant
  let M := max D C.toReal
  have hM : 0 ≤ M := hD.trans (le_max_left _ _)
  refine ⟨M,hM,?_⟩
  intro F hF hF0 B A hB hA hb hreg hnorm x hx
  by_cases hx0 : x = 0
  · simp only [hx0,hF0,norm_zero]
    positivity
  by_cases hn : ‖x‖ ≤ 1
  · have hh := hd F hF.continuousOn B hB hb x hx0 hn
    calc
      _ ≤ D*B.toReal*‖x‖ := hh
      _ ≤ D*B.toReal := by nlinarith [mul_nonneg hD (ENNReal.toReal_nonneg (a := B))]
      _ ≤ M*B.toReal := mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg
      _ ≤ M*(B.toReal+A.toReal) := by nlinarith [mul_nonneg hM (ENNReal.toReal_nonneg (a := A))]
  · have hxK : x ∈ K := ⟨hx,by simpa only [mem_ball,dist_zero_right,not_lt] using (le_of_lt (lt_of_not_ge hn))⟩
    have hh := (hc F F hreg hF.continuousOn (EventuallyEq.refl _ _) x hxK).trans
      (mul_le_mul le_rfl hnorm zero_le zero_le)
    have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top hC hA) hh
    rw [ENNReal.toReal_ofReal (norm_nonneg _),ENNReal.toReal_mul] at hr
    calc
      _ ≤ C.toReal*A.toReal := hr
      _ ≤ M*A.toReal := mul_le_mul_of_nonneg_right (le_max_right _ _) ENNReal.toReal_nonneg
      _ ≤ M*(B.toReal+A.toReal) := by nlinarith [mul_nonneg hM (ENNReal.toReal_nonneg (a := B))]

#print axioms exists_weighted_H4_entrance_value_bound
end Yamabe3.Analysis.UniformElliptic
