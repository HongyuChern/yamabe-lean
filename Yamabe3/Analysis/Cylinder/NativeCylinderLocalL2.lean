import Yamabe3.Analysis.Cylinder.NativeCylinderWeakTransfer
import Yamabe3.Analysis.Cylinder.NativeCylinderPullback
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual local Euclidean L2 of a cylinder solution

Local product L2 on every bounded time interval is transported to actual
closed Euclidean shells. The weight in the square integral is exp(-2t),
which is bounded on the fixed interval. This establishes local physical
L2 without selecting an arbitrary non-joint Lp coeFn representative.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace Yamabe3.Analysis.SpherePolar

open Yamabe3.Analysis.Delaunay

def cylinderShell (a b : ℝ) : Set E :=
  {x | Real.exp (-b) ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp (-a)}

theorem measurableSet_cylinderShell (a b : ℝ) : MeasurableSet (cylinderShell a b) :=
  (isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const) |>.measurableSet

theorem cylinderShell_ne_zero {a b : ℝ} {x : E} (hx : x ∈ cylinderShell a b) : x ≠ 0 := by
  intro hzero
  change Real.exp (-b) ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp (-a) at hx
  rw [hzero, norm_zero] at hx
  exact (Real.exp_pos (-b)).not_ge hx.1

theorem cylinderPoint_mem_shell_iff (p : ℝ × S) (a b : ℝ) :
    cylinderPoint p ∈ cylinderShell a b ↔ p.1 ∈ Icc a b := by
  simp only [cylinderShell, mem_ofPred_eq, cylinderPoint_norm, Real.exp_le_exp,
    neg_le_neg_iff, mem_Icc]
  exact and_comm

theorem logCylinderWeight_shell_square {w : ℝ × S → ℝ} (a b : ℝ) :
    logCylinderWeight ((cylinderShell a b).indicator (fun x : E => cylinderLift w x ^ 2)) =
      (Icc a b ×ˢ (univ : Set S)).indicator
        (fun p : ℝ × S => Real.exp (-2 * p.1) * w p ^ 2) := by
  funext p
  have hp := cylinderPoint_mem_shell_iff p a b
  by_cases h : p.1 ∈ Icc a b
  · have hs : cylinderPoint p ∈ cylinderShell a b := hp.mpr h
    change Real.exp (-3 * p.1) *
      (cylinderShell a b).indicator (fun x : E => cylinderLift w x ^ 2) (cylinderPoint p) = _
    rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show p ∈ Icc a b ×ˢ (univ : Set S) from ⟨h, mem_univ _⟩)]
    change Real.exp (-3 * p.1) * cylinderLift w (Real.exp (-p.1) • (p.2 : E)) ^ 2 = _
    rw [cylinderLift_smul w (Real.exp_pos _) p.2, Real.log_exp, neg_neg, mul_pow,
      radialScale_exp_neg]
    have he : Real.exp (-3 * p.1) * Real.exp (p.1 / 2) ^ 2 = Real.exp (-2 * p.1) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [← mul_assoc, he]
  · have hs : cylinderPoint p ∉ cylinderShell a b := fun hs => h (hp.mp hs)
    change Real.exp (-3 * p.1) *
      (cylinderShell a b).indicator (fun x : E => cylinderLift w x ^ 2) (cylinderPoint p) = _
    rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (show p ∉ Icc a b ×ˢ (univ : Set S) from fun h' => h h'.1), mul_zero]

theorem memLp_cylinderLift_on_shell {w : ℝ × S → ℝ} (hw : Measurable w)
    (a b : ℝ) (hL2 : MemLp w 2 ((volume.restrict (Icc a b)).prod angularVolume)) :
    MemLp (cylinderLift w) 2 (volume.restrict (cylinderShell a b)) := by
  have hshell := measurableSet_cylinderShell a b
  have hI : MeasurableSet (Icc a b ×ˢ (univ : Set S)) := measurableSet_Icc.prod MeasurableSet.univ
  have hmeasure : (volume.restrict (Icc a b)).prod angularVolume =
      (volume.prod angularVolume).restrict (Icc a b ×ˢ (univ : Set S)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hmeasure] at hL2
  have hwgt : Integrable (fun p : ℝ × S => Real.exp (-2 * p.1) * w p ^ 2)
      ((volume.prod angularVolume).restrict (Icc a b ×ˢ (univ : Set S))) := by
    apply hL2.integrable_sq.bdd_mul (c := Real.exp (-2 * a)) (by fun_prop)
    filter_upwards [ae_restrict_mem hI] with p hp
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    linarith [hp.1.1]
  have hind := (integrable_indicator_iff hI).mpr hwgt
  have hm : Measurable ((cylinderShell a b).indicator (fun x : E => cylinderLift w x ^ 2)) :=
    ((measurable_cylinderLift hw).pow_const 2).indicator hshell
  have he : Integrable ((cylinderShell a b).indicator (fun x : E => cylinderLift w x ^ 2)) := by
    apply (integrable_euclidean_iff_cylinder hm).mpr
    rw [logCylinderWeight_shell_square]
    exact hind
  apply (memLp_two_iff_integrable_sq (measurable_cylinderLift hw).aestronglyMeasurable).mpr
  exact (integrable_indicator_iff hshell).mp he

theorem memLp_physicalForcing_on_shell {f : ℝ × S → ℝ} (hf : Measurable f)
    (a b : ℝ) (hL2 : MemLp f 2 ((volume.restrict (Icc a b)).prod angularVolume)) :
    MemLp (physicalForcing f) 2 (volume.restrict (cylinderShell a b)) := by
  have h := memLp_cylinderLift_on_shell hf a b hL2
  apply h.of_le_mul (c := 8 / Real.exp (-b) ^ 2)
    (measurable_physicalForcing hf).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (measurableSet_cylinderShell a b)] with x hx
  have hb : 0 < Real.exp (-b) := Real.exp_pos _
  have hsq : Real.exp (-b) ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ hb.le hx.1 2
  calc
    ‖physicalForcing f x‖ = (8 / ‖x‖ ^ 2) * ‖cylinderLift f x‖ := by
      rw [physicalForcing, norm_div, norm_mul, norm_pow, norm_norm]
      have h8 : ‖(-8 : ℝ)‖ = 8 := by norm_num
      rw [h8]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hb) hsq)
      (norm_nonneg _)

theorem cylinderShell_mem_nhds {x : E} (hx : x ≠ 0) :
    cylinderShell (-Real.log ‖x‖ - 1) (-Real.log ‖x‖ + 1) ∈ 𝓝 x := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hlow : Real.exp (-(-Real.log ‖x‖ + 1)) < ‖x‖ := by
    calc
      _ < Real.exp (Real.log ‖x‖) := Real.exp_lt_exp.mpr (by linarith)
      _ = _ := Real.exp_log hn
  have hhigh : ‖x‖ < Real.exp (-(-Real.log ‖x‖ - 1)) := by
    calc
      _ = Real.exp (Real.log ‖x‖) := (Real.exp_log hn).symm
      _ < _ := Real.exp_lt_exp.mpr (by linarith)
  exact inter_mem
    (continuous_norm.continuousAt.preimage_mem_nhds (Ici_mem_nhds hlow))
    (continuous_norm.continuousAt.preimage_mem_nhds (Iic_mem_nhds hhigh))

/-- Every genuine locally L2 joint solution/forcing pair supplies actual
Euclidean locally L2 functions at every point away from the origin. -/
theorem local_memLp_lift_and_forcing {w f : ℝ × S → ℝ}
    (hw : Measurable w) (hf : Measurable f)
    (hwl : ∀ a b, MemLp w 2 ((volume.restrict (Icc a b)).prod angularVolume))
    (hfl : ∀ a b, MemLp f 2 ((volume.restrict (Icc a b)).prod angularVolume))
    {x : E} (hx : x ≠ 0) :
    ∃ s : Set E, s ∈ 𝓝 x ∧
      MemLp (cylinderLift w) 2 (volume.restrict s) ∧
      MemLp (physicalForcing f) 2 (volume.restrict s) := by
  let a := -Real.log ‖x‖ - 1
  let b := -Real.log ‖x‖ + 1
  exact ⟨cylinderShell a b, cylinderShell_mem_nhds hx,
    memLp_cylinderLift_on_shell hw a b (hwl a b),
    memLp_physicalForcing_on_shell hf a b (hfl a b)⟩

#print axioms memLp_cylinderLift_on_shell
#print axioms local_memLp_lift_and_forcing

end Yamabe3.Analysis.SpherePolar
