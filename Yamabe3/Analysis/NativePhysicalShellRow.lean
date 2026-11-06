import Yamabe3.Analysis.NativePhysicalShellPartition
import Yamabe3.Analysis.NativePhysicalSourceDuality

/-! A collar operator row is rescaled back to its physical shell. The
L2 cost is exp(-2s), while the dual test cost is exp(-5s/2). -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic

def nativePhysicalShellRow (n : ℕ) (U : NativeCollarL2) (x : E) : ℝ :=
  Real.exp (nativeLogShellCenter n/2)*U (Real.exp (nativeLogShellCenter n) • x)

theorem nativePhysicalShellRow_memLp (n : ℕ) (U : NativeCollarL2) :
    MemLp (nativePhysicalShellRow n U) 2 (volume.restrict (nativePhysicalShell n)) := by
  have hm := (Lp.memLp U).mono_measure (Measure.restrict_mono nativeSourceShell_subset_collar le_rfl)
  have h := (memLp_comp_dilation (Real.exp_ne_zero (nativeLogShellCenter n)) hm).const_mul (Real.exp (nativeLogShellCenter n/2))
  rw [←nativePhysicalShell_dilation] at h
  exact h

private theorem volume_scale (s : ℝ) : |((Real.exp s)^Module.finrank ℝ E)⁻¹|=Real.exp (-3*s) := by
  have hd : Module.finrank ℝ E=3 := by simp [E]
  rw [hd]
  rw [abs_of_pos (inv_pos.mpr (pow_pos (Real.exp_pos _) _)),←Real.exp_nat_mul,←Real.exp_neg]
  congr 1
  ring

theorem nativePhysicalShellRow_square_integral (n : ℕ) (U : NativeCollarL2) :
    (∫x in nativePhysicalShell n,nativePhysicalShellRow n U x^2)=
      Real.exp (-2*nativeLogShellCenter n)*(∫x in nativeSourceShell,(U x)^2) := by
  let s := nativeLogShellCenter n
  simp only [nativePhysicalShellRow,mul_pow]
  rw [integral_const_mul,nativePhysicalShell_dilation]
  rw [setIntegral_comp_dilation (Real.exp_ne_zero (nativeLogShellCenter n)) nativeSourceShell (fun x => (U x)^2),volume_scale]
  have he : Real.exp (s/2)^2*Real.exp (-3*s)=Real.exp (-2*s) := by
    rw [←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    ring
  change Real.exp (s/2)^2*(Real.exp (-3*s)*(∫x in nativeSourceShell,(U x)^2))=_
  rw [←mul_assoc,he]

theorem nativePhysicalShellRow_square_bound (n : ℕ) (U : NativeCollarL2) :
    (∫x in nativePhysicalShell n,nativePhysicalShellRow n U x^2)≤
      Real.exp (-2*nativeLogShellCenter n)*‖U‖^2 := by
  rw [nativePhysicalShellRow_square_integral]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have h := setIntegral_mono_set (s := nativeSourceShell) (t := nativePoissonEntranceCollar)
    (Lp.memLp U).integrable_sq (Eventually.of_forall (fun x => sq_nonneg (U x)))
    (Eventually.of_forall (fun x hx => nativeSourceShell_subset_collar hx))
  have hn : (∫x in nativePoissonEntranceCollar,(U x)^2)=‖U‖^2 := by
    have he := native_norm_toLp_sq_eq_integral_sq (Lp.memLp U)
    rw [Lp.toLp_coeFn] at he
    exact he.symm
  exact h.trans_eq hn

theorem nativePhysicalShellRow_test_integral (n : ℕ) (U : NativeCollarL2) (φ : E → ℝ) :
    (∫x in nativePhysicalShell n,nativePhysicalShellRow n U x*φ x)=
      Real.exp (-5*nativeLogShellCenter n/2)*
        (∫x in nativeSourceShell,U x*φ (Real.exp (-nativeLogShellCenter n) • x)) := by
  let s := nativeLogShellCenter n
  have hc : (fun x : E => nativePhysicalShellRow n U x*φ x)=
      (fun x => Real.exp (s/2)*(U (Real.exp s • x)*φ (Real.exp (-s) • (Real.exp s • x)))) := by
    funext x
    rw [smul_smul,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_smul]
    dsimp only [nativePhysicalShellRow,s]
    ring
  rw [hc,integral_const_mul,nativePhysicalShell_dilation]
  have he := setIntegral_comp_dilation (Real.exp_ne_zero s) nativeSourceShell (fun x => U x*φ (Real.exp (-s) • x))
  rw [he,volume_scale,←mul_assoc,←Real.exp_add]
  congr 2
  ring

#print axioms nativePhysicalShellRow_memLp
#print axioms nativePhysicalShellRow_square_integral
#print axioms nativePhysicalShellRow_square_bound
#print axioms nativePhysicalShellRow_test_integral
end Yamabe3.Analysis.SpherePolar
