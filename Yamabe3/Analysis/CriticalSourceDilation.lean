import Yamabe3.Analysis.WeakDilationNorm

/-! Exact three-dimensional L^(6/5) dilation costs. The exponent five
halves belongs to the actual critical source norm, not an L2 norm. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem eLpNorm_exp_dilation_sixFifths (t:ℝ) (O:Set E) (u:E→ℝ) :
    eLpNorm (fun x:E=>u (Real.exp t • x)) (6/5:ℝ≥0∞)
      (volume.restrict ((fun x:E=>Real.exp t • x) ⁻¹' O))=
        ENNReal.ofReal (Real.exp (-5*t/2))*eLpNorm u (6/5:ℝ≥0∞) (volume.restrict O) := by
  have hr:Real.exp t≠0:=(Real.exp_pos t).ne'
  have hmap:MeasurableEmbedding (fun x:E=>Real.exp t • x):=
    (Homeomorph.smulOfNeZero (Real.exp t) hr:E≃ₜE).measurableEmbedding
  change eLpNorm (u ∘ (fun x:E=>Real.exp t • x)) (6/5:ℝ≥0∞) _=_
  rw [←hmap.eLpNorm_map_measure,map_restrict_volume_dilation hr,
    eLpNorm_smul_measure_of_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr
      (abs_pos.mpr (inv_ne_zero (pow_ne_zero _ hr)))))]
  simp only [finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul]
  have he:|(Real.exp t^3)⁻¹|=Real.exp (-3*t):=by
    rw [abs_of_pos (inv_pos.mpr (pow_pos (Real.exp_pos t) 3)),←Real.exp_nat_mul,←Real.exp_neg]
    congr 1
    norm_num
  have hp:(1/(6/5:ℝ≥0∞)).toReal=(5/6:ℝ):=by norm_num
  rw [he,hp,ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),←Real.exp_mul]
  congr 2
  ring

theorem eLpNorm_exp_amplitude_dilation_sixFifths (c t:ℝ) (O:Set E) (u:E→ℝ) :
    eLpNorm (fun x:E=>Real.exp c*u (Real.exp t • x)) (6/5:ℝ≥0∞)
      (volume.restrict ((fun x:E=>Real.exp t • x) ⁻¹' O))=
        ENNReal.ofReal (Real.exp (c-5*t/2))*eLpNorm u (6/5:ℝ≥0∞) (volume.restrict O) := by
  change eLpNorm (Real.exp c • (fun x:E=>u (Real.exp t • x))) (6/5:ℝ≥0∞) _=_
  rw [eLpNorm_const_smul,Real.enorm_eq_ofReal (Real.exp_pos _).le,eLpNorm_exp_dilation_sixFifths]
  rw [←mul_assoc,←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add]
  congr 2
  ring

theorem eLpNorm_exp_cutoff_source_rescaling (a:ℝ) (ha:0<a) (s:ℝ) (O:Set E) (u:E→ℝ) :
    eLpNorm (fun x:E=>Real.exp (-2*Real.log a+s/2)*u (Real.exp (s-Real.log a) • x)) (6/5:ℝ≥0∞)
      (volume.restrict ((fun x:E=>Real.exp (s-Real.log a) • x) ⁻¹' O))=
        ENNReal.ofReal (Real.sqrt a*Real.exp (-2*s))*eLpNorm u (6/5:ℝ≥0∞) (volume.restrict O) := by
  rw [eLpNorm_exp_amplitude_dilation_sixFifths]
  have he:Real.exp (-2*Real.log a+s/2-5*(s-Real.log a)/2)=Real.sqrt a*Real.exp (-2*s):=by
    rw [show -2*Real.log a+s/2-5*(s-Real.log a)/2=Real.log a/2+(-2*s) by ring,
      Real.exp_add,Real.exp_half,Real.exp_log ha]
  rw [he]

#print axioms eLpNorm_exp_dilation_sixFifths
#print axioms eLpNorm_exp_amplitude_dilation_sixFifths
#print axioms eLpNorm_exp_cutoff_source_rescaling
end Yamabe3.Analysis.UniformElliptic
