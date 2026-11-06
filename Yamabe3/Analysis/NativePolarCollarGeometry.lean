import Yamabe3.Analysis.NativePolarTimeWindow
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The actual log-time collar is a precompact open Euclidean annulus
containing the unit sphere; closure inclusions keep a positive puncture distance. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Topology
namespace Yamabe3.Analysis.SpherePolar

theorem nativePolarTimeWindow_norm (a : ℝ) (x : E) :
    x ∈ nativePolarTimeWindow (Ioo (-a) a) ↔ Real.exp (-a) < ‖x‖ ∧ ‖x‖ < Real.exp a := by
  constructor
  · rintro ⟨hx,hlo,hhi⟩
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    exact ⟨(Real.lt_log_iff_exp_lt hn).mp (by linarith),
      (Real.log_lt_iff_lt_exp hn).mp (by linarith)⟩
  · rintro ⟨hlo,hhi⟩
    have hn : 0 < ‖x‖ := (Real.exp_pos _).trans hlo
    refine ⟨norm_pos_iff.mp hn,?_,?_⟩
    · have h := (Real.log_lt_iff_lt_exp hn).mpr hhi
      linarith
    · have h := (Real.lt_log_iff_exp_lt hn).mpr hlo
      linarith

theorem nativePolarTimeWindow_open (a : ℝ) : IsOpen (nativePolarTimeWindow (Ioo (-a) a)) := by
  have he : nativePolarTimeWindow (Ioo (-a) a) = {x : E|Real.exp (-a)<‖x‖ ∧ ‖x‖<Real.exp a} :=
    Set.ext (nativePolarTimeWindow_norm a)
  rw [he]
  exact (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem nativePolarTimeWindow_closure_bounds (a : ℝ) {x : E}
    (hx : x ∈ closure (nativePolarTimeWindow (Ioo (-a) a))) :
    Real.exp (-a) ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp a := by
  apply closure_minimal (t := {x : E|Real.exp (-a)≤‖x‖ ∧ ‖x‖≤Real.exp a}) _
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)) hx
  intro y hy
  have h := (nativePolarTimeWindow_norm a y).mp hy
  exact ⟨h.1.le,h.2.le⟩

theorem nativePolarTimeWindow_precompact (a : ℝ) :
    IsCompact (closure (nativePolarTimeWindow (Ioo (-a) a))) := by
  apply (isCompact_closedBall (0:E) (Real.exp a)).of_isClosed_subset isClosed_closure
  intro x hx
  simpa only [Metric.mem_closedBall,dist_zero_right] using (nativePolarTimeWindow_closure_bounds a hx).2

theorem nativePolarTimeWindow_closure_offZero (a : ℝ) :
    closure (nativePolarTimeWindow (Ioo (-a) a)) ⊆ ({0}ᶜ : Set E) := by
  intro x hx
  have hn := (Real.exp_pos (-a)).trans_le (nativePolarTimeWindow_closure_bounds a hx).1
  exact norm_pos_iff.mp hn

theorem nativePolarTimeWindow_nested {a b : ℝ} (hab : a < b) :
    closure (nativePolarTimeWindow (Ioo (-a) a)) ⊆ nativePolarTimeWindow (Ioo (-b) b) := by
  intro x hx
  apply (nativePolarTimeWindow_norm b x).mpr
  have h := nativePolarTimeWindow_closure_bounds a hx
  exact ⟨(Real.exp_lt_exp.mpr (neg_lt_neg hab)).trans_le h.1,
    h.2.trans_lt (Real.exp_lt_exp.mpr hab)⟩

theorem sphere_mem_nativePolarTimeWindow {a : ℝ} (ha : 0 < a) (θ : S) :
    (θ:E) ∈ nativePolarTimeWindow (Ioo (-a) a) := by
  apply (nativePolarTimeWindow_norm a (θ:E)).mpr
  rw [norm_eq_of_mem_sphere θ]
  exact ⟨by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (neg_lt_zero.mpr ha),
    by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr ha⟩

#print axioms nativePolarTimeWindow_precompact
#print axioms nativePolarTimeWindow_nested
#print axioms sphere_mem_nativePolarTimeWindow
end Yamabe3.Analysis.SpherePolar
