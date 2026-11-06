import Yamabe3.Analysis.WeakH4JetBound
import Yamabe3.Analysis.NativeAllScaleH4

/-! The same weighted H4 representative has the full first-jet decay at
zero. The constants precede the function and its all-scale bound. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric
open scoped ENNReal ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_weighted_H4_first_jet_decay_constant :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : E → ℝ), ContinuousOn u ({(0:E)}ᶜ) →
      ∀ B : ℝ≥0∞, B ≠ ⊤ →
      (∀ s : ℝ, -Real.log 2 ≤ s → MemWkp 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ∧
        iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ≤ B) →
      ∀ x : E, x ≠ 0 → ‖x‖ ≤ 1 →
        ‖u x‖ ≤ D*B.toReal*‖x‖*Real.sqrt ‖x‖ ∧
        ‖fderiv ℝ u x‖ ≤ D*B.toReal*Real.sqrt ‖x‖ := by
  have hK : sphere (0:E) 1 ⊆ halfEndBasicAnnulus := by
    intro x hx
    have hn : ‖x‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hx
    change (1/2:ℝ) < ‖x‖ ∧ ‖x‖ < 2
    rw [hn]
    norm_num
  obtain ⟨D,hD,hb⟩ := exists_weak_H4_two_jet_bound_on_compact (isCompact_sphere (0:E) 1)
    halfEndBasicAnnulus_isOpen hK
  refine ⟨D.toReal,ENNReal.toReal_nonneg,?_⟩
  intro u hu B hB hall x hx hn
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let s := -Real.log ‖x‖
  have hs0 : 0 ≤ s := neg_nonneg.mpr (Real.log_nonpos (norm_nonneg x) hn)
  have hs : -Real.log 2 ≤ s := (neg_nonpos.mpr (Real.log_nonneg (by norm_num))).trans hs0
  let y := ‖x‖⁻¹ • x
  have hy : ‖y‖ = 1 := by simp only [y,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hxpos).le,inv_mul_cancel₀ hxpos.ne']
  have hym : y ∈ sphere (0:E) 1 := by simpa only [mem_sphere,dist_zero_right] using hy
  have hc : ContinuousOn (weightedPhysicalDilation s u) halfEndBasicAnnulus := by
    apply continuousOn_const.mul
    apply hu.comp (continuous_id.const_smul (Real.exp (-s))).continuousOn
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      have hzn : (1/2:ℝ) < ‖z‖ := hz.1
      norm_num [h] at hzn
    change Real.exp (-s) • z ≠ 0
    exact smul_ne_zero (Real.exp_pos (-s)).ne' hz0
  have hbnd (j:ℕ) (hj:j ≤ 2) := (hb _ _ (hall s hs).1 hc (EventuallyEq.refl _ _) j hj y hym).trans
    (mul_le_mul le_rfl (hall s hs).2 zero_le zero_le)
  have hxy : Real.exp (-s) • y = x := by
    simp only [s,neg_neg,Real.exp_log hxpos,y,smul_smul,mul_inv_cancel₀ hxpos.ne',one_smul]
  have hex : Real.exp (-s) = ‖x‖ := by simp only [s,neg_neg,Real.exp_log hxpos]
  have hhalf : Real.exp (-s/2) = Real.sqrt ‖x‖ := by rw [Real.exp_half,hex]
  have hthree : Real.exp (-(3*s/2)) = ‖x‖*Real.sqrt ‖x‖ := by
    rw [show -(3*s/2) = -s+(-s/2) by ring,Real.exp_add,hex,hhalf]
  have hnorm : ‖weightedPhysicalDilation s u y‖ = Real.exp (3*s/2)*‖u x‖ := by
    simp only [weightedPhysicalDilation,hxy,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
  have hfd : fderiv ℝ (weightedPhysicalDilation s u) y = Real.exp (s/2) • fderiv ℝ u x := by
    change fderiv ℝ (Real.exp (3*s/2) • (fun z=>u (Real.exp (-s) • z))) y = _
    rw [fderiv_const_smul_field]
    change Real.exp (3*s/2) • fderiv ℝ (fun z=>u (Real.exp (-s) • z)) y = _
    rw [fderiv_comp_smul,hxy,smul_smul,← Real.exp_add,show 3*s/2 + -s = s/2 by ring]
  have hzero := hbnd 0 (by norm_num)
  rw [norm_iteratedFDeriv_zero,hnorm] at hzero
  have hz := ENNReal.toReal_mono (ENNReal.mul_ne_top hD hB) hzero
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)),ENNReal.toReal_mul] at hz
  have hone := hbnd 1 (by norm_num)
  rw [norm_iteratedFDeriv_one,hfd,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le] at hone
  have ho := ENNReal.toReal_mono (ENNReal.mul_ne_top hD hB) hone
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)),ENNReal.toReal_mul] at ho
  constructor
  · have hh := mul_le_mul_of_nonneg_left hz (Real.exp_pos (-(3*s/2))).le
    rw [← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul,hthree] at hh
    nlinarith only [hh]
  · have hh := mul_le_mul_of_nonneg_left ho (Real.exp_pos (-s/2)).le
    rw [← mul_assoc,← Real.exp_add,show -s/2+s/2=0 by ring,Real.exp_zero,one_mul,hhalf] at hh
    nlinarith only [hh]

#print axioms exists_weighted_H4_first_jet_decay_constant
end Yamabe3.Analysis.UniformElliptic
