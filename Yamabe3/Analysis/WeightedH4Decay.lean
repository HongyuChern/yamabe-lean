import Yamabe3.Analysis.WeakH4SupBound
import Yamabe3.Analysis.NativeAllScaleH4

/-! The all-scale weak H4 bound gives real pointwise decay at the removed
origin, for the same continuous representative. It is then extended by
zero continuously; no pointwise value is read from an arbitrary L2 class. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric
open scoped ENNReal ContDiff Topology BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_weighted_H4_decay_constant :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : E → ℝ), ContinuousOn u ({(0:E)}ᶜ) →
      ∀ B : ℝ≥0∞, B ≠ ⊤ →
      (∀ s : ℝ, -Real.log 2 ≤ s → MemWkp 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ∧
        iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ≤ B) →
      ∀ x : E, x ≠ 0 → ‖x‖ ≤ 1 → ‖u x‖ ≤ D*B.toReal*‖x‖ := by
  have hK : sphere (0:E) 1 ⊆ halfEndBasicAnnulus := by
    intro x hx
    have hn : ‖x‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hx
    change (1/2:ℝ) < ‖x‖ ∧ ‖x‖ < 2
    rw [hn]
    norm_num
  obtain ⟨D,hD,hb⟩ := exists_weak_H4_sup_bound_on_compact (isCompact_sphere (0:E) 1)
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
  have hbnd := (hb _ _ (hall s hs).1 hc (EventuallyEq.refl _ _) y hym).trans
    (mul_le_mul le_rfl (hall s hs).2 zero_le zero_le)
  have hxy : Real.exp (-s) • y = x := by
    simp only [s,neg_neg,Real.exp_log hxpos,y,smul_smul,mul_inv_cancel₀ hxpos.ne',one_smul]
  have hnorm : ‖weightedPhysicalDilation s u y‖ = Real.exp (3*s/2)*‖u x‖ := by
    simp only [weightedPhysicalDilation,hxy,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [hnorm] at hbnd
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top hD hB) hbnd
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)),ENNReal.toReal_mul] at hr
  have he : ‖x‖⁻¹ ≤ Real.exp (3*s/2) := by
    calc
      _ = Real.exp s := by
        change _ = Real.exp (-Real.log ‖x‖)
        rw [Real.exp_neg,Real.exp_log hxpos]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hi : ‖x‖⁻¹*‖u x‖ ≤ D.toReal*B.toReal :=
    (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans hr
  have hh := mul_le_mul_of_nonneg_left hi hxpos.le
  calc
    _ = ‖x‖*(‖x‖⁻¹*‖u x‖) := by rw [← mul_assoc,mul_inv_cancel₀ hxpos.ne',one_mul]
    _ ≤ ‖x‖*(D.toReal*B.toReal) := hh
    _ = _ := by ring

def zeroAtOrigin (u : E → ℝ) (x : E) : ℝ := if x = 0 then 0 else u x

theorem continuous_zeroAtOrigin {u : E → ℝ} (hu : ContinuousOn u ({(0:E)}ᶜ))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x : E, x ≠ 0 → ‖x‖ ≤ 1 → ‖u x‖ ≤ M*‖x‖) :
    Continuous (zeroAtOrigin u) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    let δ := min 1 (ε/(M+1))
    have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε (by linarith))
    refine ⟨δ,hδ,?_⟩
    intro y hy
    have hyn : ‖y‖ < δ := by simpa only [dist_zero_right] using hy
    have hy1 : ‖y‖ ≤ 1 := (hyn.trans_le (min_le_left _ _)).le
    have hyε : ‖y‖ < ε/(M+1) := hyn.trans_le (min_le_right _ _)
    have hsmall : M*‖y‖ < ε := by
      have hh := (lt_div_iff₀ (by linarith : 0 < M+1)).mp hyε
      nlinarith [norm_nonneg y]
    by_cases hy0 : y = 0
    · simp [zeroAtOrigin,hy0,hε]
    · simpa [zeroAtOrigin,hy0] using (hb y hy0 hy1).trans_lt hsmall
  · have hxP : x ∈ ({(0:E)}ᶜ : Set E) := hx
    have he : zeroAtOrigin u =ᶠ[𝓝 x] u := by
      filter_upwards [(isClosed_singleton.isOpen_compl : IsOpen ({(0:E)}ᶜ)).mem_nhds hxP] with y hy
      exact if_neg hy
    exact (hu.continuousAt ((isClosed_singleton.isOpen_compl : IsOpen ({(0:E)}ᶜ)).mem_nhds hxP)).congr he.symm

#print axioms exists_weighted_H4_decay_constant
#print axioms continuous_zeroAtOrigin
end Yamabe3.Analysis.UniformElliptic
