import Yamabe3.Analysis.NativeOuterWindowReconstruction
import Yamabe3.Analysis.NativeShellWeightedPolar

/-! The actual disjoint physical shells of a finite exterior window.
Half-open endpoints and zero exclusion are retained exactly. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar

def nativeScaledSourceShell (s:ℝ):Set E := (fun x:E=>Real.exp s • x) ⁻¹' nativeSourceShell

theorem nativeScaledSourceShell_measurable (s:ℝ) : MeasurableSet (nativeScaledSourceShell s) :=
  nativeSourceShell_measurable.preimage (continuous_const_smul (Real.exp s)).measurable

theorem nativeScaledSourceShell_mem (s:ℝ) (x:E) :
    x∈nativeScaledSourceShell s ↔ x≠0 ∧ -Real.log ‖x‖-s∈Ioc (-(1/4:ℝ)) (1/4) := by
  change (Real.exp s • x≠0 ∧ -Real.log ‖Real.exp s • x‖∈Ioc (-(1/4:ℝ)) (1/4)) ↔ _
  by_cases hx:x=0
  · simp [hx]
  · have hn:‖x‖≠0 := norm_ne_zero_iff.mpr hx
    have he:Real.exp s • x≠0 := smul_ne_zero (Real.exp_ne_zero s) hx
    rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos s).le,Real.log_mul (Real.exp_ne_zero s) hn,Real.log_exp]
    rw [show -(s+Real.log ‖x‖)= -Real.log ‖x‖-s by ring]
    exact ⟨fun h=>⟨hx,h.2⟩,fun h=>⟨he,h.2⟩⟩

theorem nativeScaledOuterShell_mem (n:ℕ) (x:E) :
    x∈nativeScaledSourceShell (nativeOuterLogShellCenter n) ↔
      x≠0 ∧ -Real.log ‖x‖∈nativeOuterLogShellInterval n := by
  rw [nativeScaledSourceShell_mem]
  exact and_congr_right (fun _=>nativeOuterLogShell_membership n (-Real.log ‖x‖))

theorem nativeScaledOuterShell_disjoint (m:ℕ) :
    Pairwise (fun i j:Fin m=>Disjoint (nativeScaledSourceShell (nativeOuterLogShellCenter i))
      (nativeScaledSourceShell (nativeOuterLogShellCenter j))) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hi hj
  exact disjoint_left.mp (nativeOuterLogWindow_disjoint m hij)
    ((nativeScaledOuterShell_mem i x).mp hi).2 ((nativeScaledOuterShell_mem j x).mp hj).2

theorem nativeScaledOuterWindow_union (m:ℕ) :
    (⋃i:Fin m,nativeScaledSourceShell (nativeOuterLogShellCenter i))=
      nativePolarTimeWindow (Ioc (-(m:ℝ)/2) 0) := by
  ext x
  simp only [mem_iUnion,nativeScaledOuterShell_mem]
  change (∃i:Fin m,x≠0 ∧ -Real.log ‖x‖∈nativeOuterLogShellInterval i) ↔
    x≠0 ∧ -Real.log ‖x‖∈Ioc (-(m:ℝ)/2) 0
  rw [←nativeOuterLogWindow_union m]
  simp only [mem_iUnion,exists_and_left]

theorem nativeScaledSourceShell_inverse_preimage (s:ℝ) :
    (fun y:E=>Real.exp (-s) • y) ⁻¹' nativeScaledSourceShell s=nativeSourceShell := by
  ext y
  change Real.exp s • (Real.exp (-s) • y)∈nativeSourceShell ↔ y∈nativeSourceShell
  rw [smul_smul,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul]

#print axioms nativeScaledSourceShell_mem
#print axioms nativeScaledOuterShell_disjoint
#print axioms nativeScaledOuterWindow_union
#print axioms nativeScaledSourceShell_inverse_preimage
end Yamabe3.Analysis.SpherePolar
