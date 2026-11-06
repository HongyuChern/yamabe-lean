import Yamabe3.Analysis.NativeLogShellIntegrals
import Yamabe3.Analysis.NativeAllScaleLocalH2

/-! Disjoint physical shells are the actual positive-time polar windows.
Their dilation is exact, including the puncture and half-open endpoints. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic

def nativePhysicalShell (n : ℕ) : Set E := nativePolarTimeWindow (nativeLogShellInterval n)

theorem nativePhysicalShell_measurable (n : ℕ) : MeasurableSet (nativePhysicalShell n) :=
  nativePolarTimeWindow_measurable measurableSet_Ioc

theorem nativePhysicalShell_union : (⋃n : ℕ,nativePhysicalShell n)=Metric.ball 0 1 \ {(0:E)} := by
  ext x
  constructor
  · intro hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    have ht : -Real.log ‖x‖∈Ioi (0:ℝ) := by
      rw [←nativeLogShellInterval_union]
      exact mem_iUnion.mpr ⟨n,hn.2⟩
    refine ⟨?_,hn.1⟩
    rw [Metric.mem_ball,dist_zero_right]
    exact (Real.log_neg_iff (norm_pos_iff.mpr hn.1)).mp (neg_pos.mp ht)
  · intro hx
    have hn : x≠0 := hx.2
    have hnorm : ‖x‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hx.1
    have ht : -Real.log ‖x‖∈Ioi (0:ℝ) := neg_pos.mpr ((Real.log_neg_iff (norm_pos_iff.mpr hn)).mpr hnorm)
    rw [←nativeLogShellInterval_union] at ht
    obtain ⟨n,hnn⟩ := mem_iUnion.mp ht
    exact mem_iUnion.mpr ⟨n,hn,hnn⟩

theorem nativePhysicalShell_disjoint : Pairwise (fun i j => Disjoint (nativePhysicalShell i) (nativePhysicalShell j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hi hj
  exact (disjoint_left.mp (nativeLogShellInterval_disjoint hij)) hi.2 hj.2

theorem nativePhysicalShell_dilation (n : ℕ) :
    nativePhysicalShell n=(fun x : E => Real.exp (nativeLogShellCenter n) • x) ⁻¹' nativeSourceShell := by
  ext x
  by_cases hx : x=0
  · subst x
    simp [nativePhysicalShell,nativePolarTimeWindow,nativeSourceShell]
  · have hn : 0<‖x‖ := norm_pos_iff.mpr hx
    have hscaled : Real.exp (nativeLogShellCenter n) • x≠0 := smul_ne_zero (Real.exp_ne_zero _) hx
    have hlog : -Real.log ‖Real.exp (nativeLogShellCenter n) • x‖=
        -Real.log ‖x‖-nativeLogShellCenter n := by
      rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,Real.log_mul (Real.exp_ne_zero _) hn.ne',Real.log_exp]
      ring
    change (x≠0 ∧ -Real.log ‖x‖∈nativeLogShellInterval n) ↔
      (Real.exp (nativeLogShellCenter n) • x≠0 ∧ -Real.log ‖Real.exp (nativeLogShellCenter n) • x‖∈Ioc (-(1/4:ℝ)) (1/4))
    rw [hlog,and_iff_right hx,and_iff_right hscaled]
    exact (nativeLogShell_membership n (-Real.log ‖x‖)).symm

theorem nativePhysicalShell_subset_window (n : ℕ) :
    nativePhysicalShell n⊆nativePhysicalScaleWindow (nativeLogShellCenter n) := by
  rw [nativePhysicalShell_dilation]
  exact preimage_mono nativeSourceShell_subset_collar

#print axioms nativePhysicalShell_union
#print axioms nativePhysicalShell_disjoint
#print axioms nativePhysicalShell_dilation
#print axioms nativePhysicalShell_subset_window
end Yamabe3.Analysis.SpherePolar
