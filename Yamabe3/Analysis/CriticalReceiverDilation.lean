import Yamabe3.Analysis.CriticalSourceDilation

/-! The receiving L6-to-local-L2 scaling pays R^(-1/2) in dimension
three. It is not a derivative bound or a contraction by itself. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem eLpNorm_exp_dilation_six (t:ℝ) (O:Set E) (u:E→ℝ) :
    eLpNorm (fun x:E=>u (Real.exp t • x)) 6
      (volume.restrict ((fun x:E=>Real.exp t • x) ⁻¹' O))=
        ENNReal.ofReal (Real.exp (-t/2))*eLpNorm u 6 (volume.restrict O) := by
  have hr:Real.exp t≠0:=(Real.exp_pos t).ne'
  have hmap:MeasurableEmbedding (fun x:E=>Real.exp t • x):=
    (Homeomorph.smulOfNeZero (Real.exp t) hr:E≃ₜE).measurableEmbedding
  change eLpNorm (u ∘ (fun x:E=>Real.exp t • x)) 6 _=_
  rw [←hmap.eLpNorm_map_measure,map_restrict_volume_dilation hr,
    eLpNorm_smul_measure_of_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr
      (abs_pos.mpr (inv_ne_zero (pow_ne_zero _ hr)))))]
  simp only [finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul]
  have he:|(Real.exp t^3)⁻¹|=Real.exp (-3*t):=by
    rw [abs_of_pos (inv_pos.mpr (pow_pos (Real.exp_pos t) 3)),←Real.exp_nat_mul,←Real.exp_neg]
    congr 1
    norm_num
  have hp:(1/(6:ℝ≥0∞)).toReal=(1/6:ℝ):=by norm_num
  rw [he,hp,ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),←Real.exp_mul]
  congr 2
  ring

theorem exists_criticalReceiver_dilation_L2_bound (O:Set E) (hvol:volume O<⊤) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀u:E→ℝ,MemLp u 6 volume→∀t:ℝ,
      MemLp (fun x:E=>u (Real.exp t • x)) 2 (volume.restrict O) ∧
      eLpNorm (fun x:E=>u (Real.exp t • x)) 2 (volume.restrict O)≤
        C*ENNReal.ofReal (Real.exp (-t/2))*eLpNorm u 6 volume := by
  letI:IsFiniteMeasure (volume.restrict O):=⟨by simpa only [Measure.restrict_apply_univ] using hvol⟩
  refine ⟨(volume O)^(1/3:ℝ),ENNReal.rpow_ne_top_of_nonneg (by norm_num) hvol.ne,fun u hu t=>?_⟩
  have hm:MemLp (fun x:E=>u (Real.exp t • x)) 6 volume:=by
    simpa only [preimage_univ,Measure.restrict_univ] using
      memLp_comp_dilation (Real.exp_pos t).ne' (hu.restrict univ)
  have hs:eLpNorm (fun x:E=>u (Real.exp t • x)) 6 volume=
      ENNReal.ofReal (Real.exp (-t/2))*eLpNorm u 6 volume:=by
    simpa only [preimage_univ,Measure.restrict_univ] using eLpNorm_exp_dilation_six t univ u
  have hh:=hm.restrict O
  have hn:=eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num:(2:ℝ≥0∞)≤6) hh.1
  have he:1/(2:ℝ≥0∞).toReal-1/(6:ℝ≥0∞).toReal=(1/3:ℝ):=by norm_num
  rw [he,Measure.restrict_apply_univ] at hn
  refine ⟨hh.mono_exponent (by norm_num),hn.trans ?_⟩
  calc
    _ ≤ eLpNorm (fun x:E=>u (Real.exp t • x)) 6 volume*(volume O)^(1/3:ℝ):=
      mul_le_mul (eLpNorm_mono_measure _ Measure.restrict_le_self) le_rfl zero_le zero_le
    _ = _:=by rw [hs];ring

#print axioms eLpNorm_exp_dilation_six
#print axioms exists_criticalReceiver_dilation_L2_bound
end Yamabe3.Analysis.UniformElliptic
