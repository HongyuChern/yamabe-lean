import Yamabe3.Analysis.ExteriorPowerCriticalTail

/-! Exact scale invariance of the three-dimensional L^(3/2) potential
norm. Shrinking the physical entrance does not itself make this norm small. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem eLpNorm_exp_potential_dilation (t : ℝ) (q : E → ℝ) :
    eLpNorm (fun x : E => Real.exp (-2*t)*q (Real.exp (-t) • x)) (3/2 : ℝ≥0∞) volume =
      eLpNorm q (3/2 : ℝ≥0∞) volume := by
  have hmap : MeasurableEmbedding (fun x : E => Real.exp (-t) • x) :=
    (Homeomorph.smulOfNeZero (Real.exp (-t)) (Real.exp_pos _).ne' : E ≃ₜ E).measurableEmbedding
  have hd : eLpNorm (fun x : E => q (Real.exp (-t) • x)) (3/2 : ℝ≥0∞) volume =
      (ENNReal.ofReal |(Real.exp (-t)^3)⁻¹|)^((1/(3/2 : ℝ≥0∞)).toReal)*eLpNorm q (3/2 : ℝ≥0∞) volume := by
    change eLpNorm (q ∘ (fun x : E => Real.exp (-t) • x)) _ _ = _
    rw [← hmap.eLpNorm_map_measure, Measure.map_addHaar_smul volume (Real.exp_pos (-t)).ne',
      eLpNorm_smul_measure_of_ne_zero (by positivity)]
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  change eLpNorm (Real.exp (-2*t) • (fun x : E => q (Real.exp (-t) • x))) _ _ = _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (Real.exp_pos _).le, hd]
  have hfac : |(Real.exp (-t)^3)⁻¹| = Real.exp (3*t) := by
    rw [abs_of_pos (inv_pos.mpr (pow_pos (Real.exp_pos _) _)), ← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    ring
  rw [hfac, show (1/(3/2 : ℝ≥0∞)).toReal = (2/3 : ℝ) by norm_num,
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
    ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
    show -2*t+(3*t)*(2/3)=0 by ring, Real.exp_zero, ENNReal.ofReal_one, one_mul]

theorem memLp_exp_potential_dilation (t : ℝ) (q : E → ℝ)
    (hq : MemLp q (3/2 : ℝ≥0∞) volume) :
    MemLp (fun x : E => Real.exp (-2*t)*q (Real.exp (-t) • x)) (3/2 : ℝ≥0∞) volume := by
  have hm : MemLp (fun x : E => q (Real.exp (-t) • x)) (3/2 : ℝ≥0∞) volume := by
    simpa only [preimage_univ, Measure.restrict_univ] using
      (memLp_comp_dilation (Real.exp_pos (-t)).ne' (O := univ)
        (by simpa only [Measure.restrict_univ] using hq))
  exact hm.const_mul _

#print axioms eLpNorm_exp_potential_dilation
#print axioms memLp_exp_potential_dilation
end Yamabe3.Analysis.UniformElliptic
