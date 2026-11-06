import Yamabe3.Analysis.Cylinder.NativeCylinderLocalL2

/-! # Genuine precompact Euclidean annuli around every nonzero point -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Topology

namespace Yamabe3.Analysis.SpherePolar

def cylinderAnnulus (a b : ℝ) : Set E :=
  {x | Real.exp (-b) < ‖x‖ ∧ ‖x‖ < Real.exp (-a)}

theorem isOpen_cylinderAnnulus (a b : ℝ) : IsOpen (cylinderAnnulus a b) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem isClosed_cylinderShell (a b : ℝ) : IsClosed (cylinderShell a b) :=
  (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)

theorem isCompact_cylinderShell (a b : ℝ) : IsCompact (cylinderShell a b) := by
  apply (isCompact_closedBall (0 : E) (Real.exp (-a))).of_isClosed_subset
    (isClosed_cylinderShell a b)
  intro x hx
  simpa only [mem_closedBall, dist_zero_right] using hx.2

theorem cylinderAnnulus_subset_shell (a b : ℝ) : cylinderAnnulus a b ⊆ cylinderShell a b :=
  fun _ hx => ⟨hx.1.le, hx.2.le⟩

theorem closure_cylinderAnnulus_subset_shell (a b : ℝ) :
    closure (cylinderAnnulus a b) ⊆ cylinderShell a b :=
  (isClosed_cylinderShell a b).closure_subset_iff.mpr (cylinderAnnulus_subset_shell a b)

theorem isCompact_closure_cylinderAnnulus (a b : ℝ) :
    IsCompact (closure (cylinderAnnulus a b)) :=
  (isCompact_cylinderShell a b).of_isClosed_subset isClosed_closure
    (closure_cylinderAnnulus_subset_shell a b)

theorem closure_cylinderAnnulus_subset_punctured (a b : ℝ) :
    closure (cylinderAnnulus a b) ⊆ ({0}ᶜ : Set E) := by
  intro x hx
  exact cylinderShell_ne_zero (closure_cylinderAnnulus_subset_shell a b hx)

theorem closure_cylinderAnnulus_subset_wider {a b a' b' : ℝ}
    (ha : a < a') (hb : b' < b) :
    closure (cylinderAnnulus a' b') ⊆ cylinderAnnulus a b := by
  intro x hx
  have h := closure_cylinderAnnulus_subset_shell a' b' hx
  exact ⟨(Real.exp_lt_exp.mpr (neg_lt_neg hb)).trans_le h.1,
    h.2.trans_lt (Real.exp_lt_exp.mpr (neg_lt_neg ha))⟩

theorem mem_cylinderAnnulus_of_log_norm {a b : ℝ} {x : E} (hx : x ≠ 0)
    (ha : a < -Real.log ‖x‖) (hb : -Real.log ‖x‖ < b) :
    x ∈ cylinderAnnulus a b := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  constructor
  · calc
      Real.exp (-b) < Real.exp (Real.log ‖x‖) := Real.exp_lt_exp.mpr (by linarith)
      _ = ‖x‖ := Real.exp_log hn
  · calc
      ‖x‖ = Real.exp (Real.log ‖x‖) := (Real.exp_log hn).symm
      _ < Real.exp (-a) := Real.exp_lt_exp.mpr (by linarith)

theorem cylinderAnnulus_mem_nhds {x : E} (hx : x ≠ 0) :
    cylinderAnnulus (-Real.log ‖x‖ - 1) (-Real.log ‖x‖ + 1) ∈ 𝓝 x :=
  (isOpen_cylinderAnnulus _ _).mem_nhds
    (mem_cylinderAnnulus_of_log_norm hx (by linarith) (by linarith))

#print axioms closure_cylinderAnnulus_subset_wider
#print axioms cylinderAnnulus_mem_nhds

end Yamabe3.Analysis.SpherePolar
