import Yamabe3.Analysis.NativeShellWeightedPolar
import Yamabe3.Analysis.CriticalSourceDilation

/-! Actual zero-extended physical shell source, retaining the factor eight.
The critical dilation cost is sqrt(a)*exp(-2s).  The source is L2 as
well as L^(6/5); all equalities refer to one literal representative. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic

private theorem sourceShell_volume_finite : volume nativeSourceShell < ⊤ := by
  exact (measure_mono (nativeSourceShell_subset_collar.trans subset_closure)).trans_lt
    (nativePolarTimeWindow_precompact (1/2)).measure_lt_top

def nativeSourceShellCriticalCost : ℝ := ((volume nativeSourceShell)^(1/3:ℝ)).toReal

def nativeZeroShellSource (U:NativeCollarL2) : E → ℝ := nativeSourceShell.indicator (U:E→ℝ)

theorem nativeZeroShellSource_memLp_two (U:NativeCollarL2) :
    MemLp (nativeZeroShellSource U) 2 volume := by
  exact (memLp_indicator_iff_restrict nativeSourceShell_measurable).mpr
    ((Lp.memLp U).mono_measure (Measure.restrict_mono nativeSourceShell_subset_collar le_rfl))

theorem nativeZeroShellSource_critical_bound (U:NativeCollarL2) :
    MemLp (nativeZeroShellSource U) (6/5:ℝ≥0∞) volume ∧
      eLpNorm (nativeZeroShellSource U) (6/5:ℝ≥0∞) volume ≤
        ENNReal.ofReal (nativeSourceShellCriticalCost*‖U‖) := by
  letI:IsFiniteMeasure (volume.restrict nativeSourceShell) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using sourceShell_volume_finite⟩
  have hp:(6/5:ℝ≥0∞) ≤ 2 :=
    (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr (by norm_num)
  have hm:MemLp (U:E→ℝ) 2 (volume.restrict nativeSourceShell) :=
    (Lp.memLp U).mono_measure (Measure.restrict_mono nativeSourceShell_subset_collar le_rfl)
  refine ⟨(memLp_indicator_iff_restrict nativeSourceShell_measurable).mpr (hm.mono_exponent hp),?_⟩
  rw [nativeZeroShellSource,eLpNorm_indicator_eq_eLpNorm_restrict nativeSourceShell_measurable]
  have hn:=eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hm.1
  have he:1/(6/5:ℝ≥0∞).toReal-1/(2:ℝ≥0∞).toReal=(1/3:ℝ) := by norm_num
  rw [he,Measure.restrict_apply_univ] at hn
  have hnorm:eLpNorm (U:E→ℝ) 2 (volume.restrict nativeSourceShell) ≤ ENNReal.ofReal ‖U‖ := by
    rw [ofReal_norm,Lp.enorm_def]
    exact eLpNorm_mono_measure (U:E→ℝ) (Measure.restrict_mono nativeSourceShell_subset_collar le_rfl)
  apply (hn.trans (mul_le_mul_of_nonneg_right hnorm zero_le)).trans_eq
  have ht:((volume nativeSourceShell)^(1/3:ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) sourceShell_volume_finite.ne
  unfold nativeSourceShellCriticalCost
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal ht]
  ring

def nativePhysicalShellSource (a s:ℝ) (U:NativeCollarL2) (x:E) : ℝ :=
  8*Real.exp (-2*Real.log a+s/2)*nativeZeroShellSource U (Real.exp (s-Real.log a) • x)

theorem nativePhysicalShellSource_memLp_two (a s:ℝ) (U:NativeCollarL2) :
    MemLp (nativePhysicalShellSource a s U) 2 volume := by
  have h:=memLp_comp_dilation (Real.exp_ne_zero (s-Real.log a))
    ((nativeZeroShellSource_memLp_two U).restrict univ)
  change MemLp (fun x:E=>8*Real.exp (-2*Real.log a+s/2)*nativeZeroShellSource U (Real.exp (s-Real.log a) • x)) 2 volume
  simpa only [preimage_univ,Measure.restrict_univ] using h.const_mul (8*Real.exp (-2*Real.log a+s/2))

theorem nativePhysicalShellSource_critical_bound {a:ℝ} (ha:0<a) (s:ℝ) (U:NativeCollarL2) :
    MemLp (nativePhysicalShellSource a s U) (6/5:ℝ≥0∞) volume ∧
      eLpNorm (nativePhysicalShellSource a s U) (6/5:ℝ≥0∞) volume ≤
        ENNReal.ofReal (8*nativeSourceShellCriticalCost*Real.sqrt a*Real.exp (-2*s)*‖U‖) := by
  have hu:=nativeZeroShellSource_critical_bound U
  have hd:=memLp_comp_dilation (Real.exp_ne_zero (s-Real.log a)) (hu.1.restrict univ)
  refine ⟨?_,?_⟩
  · change MemLp (fun x:E=>8*Real.exp (-2*Real.log a+s/2)*nativeZeroShellSource U (Real.exp (s-Real.log a) • x)) (6/5:ℝ≥0∞) volume
    simpa only [preimage_univ,Measure.restrict_univ] using hd.const_mul (8*Real.exp (-2*Real.log a+s/2))
  have he:=eLpNorm_exp_cutoff_source_rescaling a ha s univ (nativeZeroShellSource U)
  simp only [preimage_univ,Measure.restrict_univ] at he
  have hf:nativePhysicalShellSource a s U=
      (8:ℝ) • (fun x:E=>Real.exp (-2*Real.log a+s/2)*nativeZeroShellSource U (Real.exp (s-Real.log a) • x)) := by
    funext x
    simp only [nativePhysicalShellSource,Pi.smul_apply,smul_eq_mul]
    ring
  rw [hf,eLpNorm_const_smul,Real.enorm_eq_ofReal (by norm_num:0≤(8:ℝ)),he]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu.2 zero_le) zero_le).trans_eq
  rw [←ENNReal.ofReal_mul (by positivity:0≤Real.sqrt a*Real.exp (-2*s)),
    ←ENNReal.ofReal_mul (by norm_num:0≤(8:ℝ))]
  congr 1
  ring

theorem nativePhysicalShellSource_zero_off (a s:ℝ) (U:NativeCollarL2) {x:E}
    (hx:Real.exp (s-Real.log a) • x ∉ nativeSourceShell) :
    nativePhysicalShellSource a s U x=0 := by
  simp only [nativePhysicalShellSource,nativeZeroShellSource,indicator_of_notMem hx,mul_zero]

#print axioms nativeZeroShellSource_memLp_two
#print axioms nativeZeroShellSource_critical_bound
#print axioms nativePhysicalShellSource_memLp_two
#print axioms nativePhysicalShellSource_critical_bound
#print axioms nativePhysicalShellSource_zero_off
end Yamabe3.Analysis.SpherePolar
