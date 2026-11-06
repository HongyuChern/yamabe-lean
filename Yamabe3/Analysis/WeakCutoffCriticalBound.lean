import Yamabe3.Analysis.WeakCutoffCommutatorBound
import Yamabe3.Analysis.CriticalSourceDilation

/-! The same actual cutoff commutator has critical L^(6/5) control,
including the exact physical rescaling and its sqrt(a) cost. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_weakCutoffCommutator_critical_bound {O:Set E} (hO:IsOpen O)
    (hOc:IsCompact (closure O)) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀u:E→ℝ,MemWkp 1 2 u O→
      MemLp (weakCutoffCommutator O χ u) (6/5:ℝ≥0∞) (volume.restrict O) ∧
      eLpNorm (weakCutoffCommutator O χ u) (6/5:ℝ≥0∞) (volume.restrict O)≤C*iteratedWeakSobolevNorm 1 2 u O := by
  obtain ⟨C,hC,hb⟩:=exists_weakCutoffCommutator_L2_bound hO hOc χ hχ
  have hvol:volume O<⊤:=(measure_mono subset_closure).trans_lt hOc.measure_lt_top
  letI:IsFiniteMeasure (volume.restrict O):=⟨by simpa only [Measure.restrict_apply_univ] using hvol⟩
  refine ⟨C*(volume O)^(1/3:ℝ),ENNReal.mul_ne_top hC
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hvol.ne),fun u hu=>?_⟩
  have hh:=hb u hu
  have h62:(6/5:ℝ≥0∞)≤2:=(ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr (by norm_num)
  have hn:=eLpNorm_le_eLpNorm_mul_rpow_measure_univ h62 hh.1.aestronglyMeasurable
  have he:1/(6/5:ℝ≥0∞).toReal-1/(2:ℝ≥0∞).toReal=(1/3:ℝ):=by norm_num
  rw [he,Measure.restrict_apply_univ] at hn
  exact ⟨hh.1.mono_exponent h62,hn.trans
    ((mul_le_mul hh.2 le_rfl zero_le zero_le).trans_eq (by ring))⟩

theorem exists_weakCutoff_scaled_critical_bound {O:Set E} (hO:IsOpen O)
    (hOc:IsCompact (closure O)) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀(u:E→ℝ),MemWkp 1 2 u O→∀(B:ℝ≥0∞) (s a:ℝ),0<a→
      iteratedWeakSobolevNorm 1 2 u O≤ENNReal.ofReal (Real.exp (2*s))*B→
      let Ephys:=fun x:E=>Real.exp (-2*Real.log a+s/2)*
        weakCutoffCommutator O χ u (Real.exp (s-Real.log a) • x)
      let Ω:=((fun x:E=>Real.exp (s-Real.log a) • x) ⁻¹' O)
      MemLp Ephys (6/5:ℝ≥0∞) (volume.restrict Ω) ∧
      eLpNorm Ephys (6/5:ℝ≥0∞) (volume.restrict Ω)≤C*ENNReal.ofReal (Real.sqrt a)*B := by
  obtain ⟨C,hC,hb⟩:=exists_weakCutoffCommutator_critical_bound hO hOc χ hχ
  refine ⟨C,hC,fun u hu B s a ha hn=>?_⟩
  have hh:=hb u hu
  refine ⟨(memLp_comp_dilation (Real.exp_pos (s-Real.log a)).ne' hh.1).const_mul _,?_⟩
  change eLpNorm (fun x:E=>Real.exp (-2*Real.log a+s/2)*weakCutoffCommutator O χ u (Real.exp (s-Real.log a) • x))
    (6/5:ℝ≥0∞) _≤_
  rw [eLpNorm_exp_cutoff_source_rescaling a ha]
  have hcoef:ENNReal.ofReal (Real.sqrt a*Real.exp (-2*s))*ENNReal.ofReal (Real.exp (2*s))=
      ENNReal.ofReal (Real.sqrt a):=by
    rw [←ENNReal.ofReal_mul (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)]
    congr 1
    rw [mul_assoc,←Real.exp_add,show -2*s+2*s=0 by ring,Real.exp_zero,mul_one]
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt a*Real.exp (-2*s))*(C*(ENNReal.ofReal (Real.exp (2*s))*B)) :=
      mul_le_mul le_rfl (hh.2.trans (mul_le_mul le_rfl hn zero_le zero_le)) zero_le zero_le
    _ = C*(ENNReal.ofReal (Real.sqrt a*Real.exp (-2*s))*ENNReal.ofReal (Real.exp (2*s)))*B := by ring
    _ = _ := by rw [hcoef]

#print axioms exists_weakCutoffCommutator_critical_bound
#print axioms exists_weakCutoff_scaled_critical_bound
end Yamabe3.Analysis.UniformElliptic
