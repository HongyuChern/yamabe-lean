import Yamabe3.W6.EuclideanPuncture
import Yamabe3.Geometry.ConformalMetricCompleteness
import Yamabe3.Geometry.OpenRestriction
import PoincareLib.Geometry.Riemannian.ScalarOperators.Euclidean
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Norm

/-!
# Completeness at both ends of the actual punctured Euclidean space

The logarithmic radius has compact absolute sublevels. Its derivative is
bounded by the Euclidean tangent norm divided by the radius. A positive
lower bound `u² ≥ c/r` therefore proves completeness of the native conformal
metric, at zero and at infinity simultaneously.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric TopologicalSpace PoincareMT
open scoped Manifold ContDiff Topology Bundle

namespace Yamabe3.W6

section Barrier

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- A smooth real function may escape to either sign; compact absolute
sublevels and a true tangent derivative bound still prove completeness. -/
theorem metricComplete_of_compact_abs_sublevels_derivative_bound
    (g : RiemannianMetric n M) (b : M → ℝ)
    (hb : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 b)
    (hcompact : ∀ R : ℝ, IsCompact {x : M | |b x| ≤ R})
    (hgrad : ∀ x v, |mvfderiv (𝓡 n) b x v| ≤ g.tangentNorm x v) :
    MetricComplete g := by
  apply Geometry.metricComplete_of_compact_barrier_sublevels g (fun x => |b x|) hcompact
  intro x y hfinite
  have he := g.edist_le_mul_edist_of_derivative_bound hb
    (K := 1) (by norm_num) (by simpa using hgrad) x y
  have he' : EDist.edist (b x) (b y) ≤ g.edist x y := by simpa using he
  have hr : |b x - b y| ≤ (g.edist x y).toReal := by
    simpa [edist_dist, Real.dist_eq] using ENNReal.toReal_mono hfinite he'
  have ht : |b x| ≤ |b x - b y| + |b y| := by
    simpa only [sub_add_cancel] using abs_add_le (b x - b y) (b y)
  linarith

end Barrier

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def logRadius (x : euclideanPuncturedOpen) : ℝ := Real.log ‖(x : E3)‖

theorem logRadius_contMDiff :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ logRadius := by
  intro x
  have hx : (x : E3) ≠ 0 := (mem_euclideanPuncturedOpen x.val).mp x.property
  have h : ContDiffAt ℝ ∞ (fun y : E3 => Real.log ‖y‖) x.val :=
    (contDiffAt_norm ℝ hx).log (norm_ne_zero_iff.mpr hx)
  exact h.contMDiffAt.comp x
    (contMDiff_subtype_val (I := 𝓡 3) (U := euclideanPuncturedOpen) (n := ∞) x)

/-- This is a compact annulus in the actual punctured Euclidean topology. -/
theorem isCompact_abs_logRadius_sublevel (R : ℝ) :
    IsCompact {x : euclideanPuncturedOpen | |logRadius x| ≤ R} := by
  apply Subtype.isCompact_iff.mpr
  have heq : ((↑) '' {x : euclideanPuncturedOpen | |logRadius x| ≤ R} : Set E3) =
      closedBall 0 (Real.exp R) ∩ {x : E3 | Real.exp (-R) ≤ ‖x‖} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hn : 0 < ‖(y : E3)‖ := norm_pos_iff.mpr
        ((mem_euclideanPuncturedOpen y.val).mp y.property)
      change |Real.log ‖(y : E3)‖| ≤ R at hy
      obtain ⟨hlo, hhi⟩ := abs_le.mp hy
      refine ⟨?_, (Real.le_log_iff_exp_le hn).mp hlo⟩
      simpa only [mem_closedBall, dist_zero_right] using
        (Real.log_le_iff_le_exp hn).mp hhi
    · rintro ⟨hhi, hlo⟩
      have hn : 0 < ‖x‖ := (Real.exp_pos (-R)).trans_le hlo
      have hx : x ∈ euclideanPuncturedOpen :=
        (mem_euclideanPuncturedOpen x).mpr (norm_pos_iff.mp hn)
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      change |Real.log ‖x‖| ≤ R
      refine abs_le.mpr ⟨(Real.le_log_iff_exp_le hn).mpr hlo, ?_⟩
      apply (Real.log_le_iff_le_exp hn).mpr
      simpa only [mem_closedBall, dist_zero_right] using hhi
  rw [heq]
  exact (isCompact_closedBall (0 : E3) (Real.exp R)).inter_right
    (isClosed_le continuous_const continuous_norm)

theorem abs_mvfderiv_logRadius_le
    (x : euclideanPuncturedOpen) (v : TangentSpace (𝓡 3) x) :
    |mvfderiv (𝓡 3) logRadius x v| ≤
      ‖(x : E3)‖⁻¹ *
        (Geometry.restrictMetric (RiemannianMetric.euclideanMetric 3)
          euclideanPuncturedOpen).tangentNorm x v := by
  let L := mfderiv (𝓡 3) (𝓡 3)
    (Subtype.val : euclideanPuncturedOpen → E3) x
  have hx : (x : E3) ≠ 0 := (mem_euclideanPuncturedOpen x.val).mp x.property
  have hn : 0 < ‖(x : E3)‖ := norm_pos_iff.mpr hx
  have hnorm : DifferentiableAt ℝ (fun y : E3 => ‖y‖) x.val :=
    (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 _ _).differentiableAt (by simp)
  have hd : mvfderiv (𝓡 3) logRadius x v =
      ‖(x : E3)‖⁻¹ * fderiv ℝ (fun y : E3 => ‖y‖) x.val (L v) := by
    change mvfderiv (𝓡 3)
      ((fun y : E3 => Real.log ‖y‖) ∘ Subtype.val) x v = _
    rw [mvfderiv_comp x (hnorm.log hn.ne').mdifferentiableAt
      ((contMDiff_subtype_val (I := 𝓡 3) (U := euclideanPuncturedOpen)
        (n := ∞) x).mdifferentiableAt (by simp))]
    simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
    rw [fderiv.log hnorm hn.ne']
    rfl
  have hN : ‖fderiv ℝ (fun y : E3 => ‖y‖) x.val‖ ≤ 1 :=
    (norm_fderiv_norm hnorm).le
  let w : E3 := L v
  have hbound : |fderiv ℝ (fun y : E3 => ‖y‖) x.val w| ≤ ‖w‖ := by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ (fun y : E3 => ‖y‖) x.val).le_opNorm w).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hN (norm_nonneg w))
  have ht : (Geometry.restrictMetric (RiemannianMetric.euclideanMetric 3)
      euclideanPuncturedOpen).tangentNorm x v = ‖w‖ := by
    change Real.sqrt (inner ℝ w w) = ‖w‖
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [hd, abs_mul, abs_of_pos (inv_pos.mpr hn), ht]
  exact mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hn.le)

/-- A global lower bound at the natural cylindrical rate controls both
ends. This is a completeness theorem, not a nonlinear existence assumption. -/
theorem euclidean_cylindrical_complete
    (u : euclideanPuncturedOpen → ℝ)
    (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u) (hpos : ∀ x, 0 < u x)
    (c : ℝ) (hc : 0 < c)
    (hlower : ∀ x : euclideanPuncturedOpen, c / ‖(x : E3)‖ ≤ u x ^ 2) :
    MetricComplete (MetricSurgery.positiveScaling
      (Geometry.restrictMetric (RiemannianMetric.euclideanMetric 3) euclideanPuncturedOpen)
      (fun x => u x ^ 4) (hu.pow 4) (fun x => pow_pos (hpos x) 4)) := by
  let g := Geometry.restrictMetric (RiemannianMetric.euclideanMetric 3) euclideanPuncturedOpen
  have hcompact (R : ℝ) :
      IsCompact {x : euclideanPuncturedOpen | |c * logRadius x| ≤ R} := by
    have heq : {x : euclideanPuncturedOpen | |c * logRadius x| ≤ R} =
        {x : euclideanPuncturedOpen | |logRadius x| ≤ R / c} := by
      ext x
      simp only [mem_setOf_eq, abs_mul, abs_of_pos hc]
      rw [le_div_iff₀ hc, mul_comm]
    rw [heq]
    exact isCompact_abs_logRadius_sublevel (R / c)
  apply metricComplete_of_compact_abs_sublevels_derivative_bound _
    (fun x => c * logRadius x)
    ((contMDiff_const.mul logRadius_contMDiff).of_le (by simp)) hcompact
  intro x v
  have hscale : mvfderiv (𝓡 3) (fun y => c * logRadius y) x v =
      c * mvfderiv (𝓡 3) logRadius x v := by
    rw [mvfderiv_fun_mul mdifferentiableAt_const
      ((logRadius_contMDiff x).mdifferentiableAt (by simp))]
    simp [mvfderiv_const]
  rw [Geometry.tangentNorm_positiveScaling_fourth g u hu hpos x v,
    hscale, abs_mul, abs_of_pos hc]
  calc
    c * |mvfderiv (𝓡 3) logRadius x v| ≤ c * (‖(x : E3)‖⁻¹ * g.tangentNorm x v) :=
      mul_le_mul_of_nonneg_left (abs_mvfderiv_logRadius_le x v) hc.le
    _ = (c / ‖(x : E3)‖) * g.tangentNorm x v := by rw [div_eq_mul_inv, mul_assoc]
    _ ≤ u x ^ 2 * g.tangentNorm x v :=
      mul_le_mul_of_nonneg_right (hlower x) (Real.sqrt_nonneg _)

#print axioms metricComplete_of_compact_abs_sublevels_derivative_bound
#print axioms isCompact_abs_logRadius_sublevel
#print axioms abs_mvfderiv_logRadius_le
#print axioms euclidean_cylindrical_complete

end Yamabe3.W6
