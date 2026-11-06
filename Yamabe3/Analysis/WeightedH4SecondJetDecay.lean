import Yamabe3.Analysis.WeightedH4FirstJetDecay

/-! The actual second derivative has the integrable r^(-1/2) bound.
Dilation is proved locally at finite regularity, without a false global
C2 assumption at the pole. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric
open scoped ENNReal ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

private theorem iterated_dilation_of_ne_zero (u:E→ℝ) (n:ℕ) {a:ℝ} (ha:a≠0) (x:E) :
    iteratedFDeriv ℝ n (fun y=>u (a • y)) x=a^n • iteratedFDeriv ℝ n u (a • x) := by
  let e:E≃L[ℝ]E:=(LinearEquiv.smulOfNeZero ℝ E a ha).toContinuousLinearEquiv
  have h:=e.iteratedFDerivWithin_comp_right u uniqueDiffOn_univ (mem_univ (e x)) n
  simp only [preimage_univ,iteratedFDerivWithin_univ] at h
  change iteratedFDeriv ℝ n (fun y=>u (a • y)) x=_ at h
  rw [h]
  ext m
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousMultilinearMap.smul_apply]
  change (iteratedFDeriv ℝ n u (a • x)) (fun i=>a • m i)=_
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp

theorem exists_weighted_H4_second_jet_decay_constant :
    ∃ D:ℝ,0 ≤ D ∧ ∀(u:E→ℝ),ContDiffOn ℝ 2 u ({(0:E)}ᶜ) →
      ∀ B:ℝ≥0∞,B≠⊤ →
      (∀s:ℝ,-Real.log 2 ≤ s → MemWkp 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ∧
        iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ≤ B) →
      ∀x:E,x≠0 → ‖x‖ ≤ 1 →
        ‖iteratedFDeriv ℝ 2 u x‖ ≤ D*B.toReal/Real.sqrt ‖x‖ := by
  have hK:sphere (0:E) 1 ⊆ halfEndBasicAnnulus:=by
    intro x hx
    have hn:‖x‖=1:=by simpa only [mem_sphere,dist_zero_right] using hx
    change (1/2:ℝ)<‖x‖ ∧ ‖x‖<2
    rw [hn]
    norm_num
  obtain ⟨D,hD,hb⟩:=exists_weak_H4_two_jet_bound_on_compact (isCompact_sphere (0:E) 1)
    halfEndBasicAnnulus_isOpen hK
  refine ⟨D.toReal,ENNReal.toReal_nonneg,?_⟩
  intro u hu B hB hall x hx hn
  have hxpos:0<‖x‖:=norm_pos_iff.mpr hx
  let s:=-Real.log ‖x‖
  have hs0:0 ≤ s:=neg_nonneg.mpr (Real.log_nonpos (norm_nonneg x) hn)
  have hs:-Real.log 2 ≤ s:=(neg_nonpos.mpr (Real.log_nonneg (by norm_num))).trans hs0
  let y:=‖x‖⁻¹ • x
  have hy:‖y‖=1:=by simp only [y,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hxpos).le,inv_mul_cancel₀ hxpos.ne']
  have hym:y∈sphere (0:E) 1:=by simpa only [mem_sphere,dist_zero_right] using hy
  have hc:ContinuousOn (weightedPhysicalDilation s u) halfEndBasicAnnulus:=by
    apply continuousOn_const.mul
    apply hu.continuousOn.comp (continuous_id.const_smul (Real.exp (-s))).continuousOn
    intro z hz
    change Real.exp (-s) • z ≠ 0
    apply smul_ne_zero (Real.exp_pos (-s)).ne'
    intro h
    have hh:=hz.1
    norm_num [h] at hh
  have hbnd:=(hb _ _ (hall s hs).1 hc (EventuallyEq.refl _ _) 2 le_rfl y hym).trans
    (mul_le_mul le_rfl (hall s hs).2 zero_le zero_le)
  have hxy:Real.exp (-s) • y=x:=by
    simp only [s,neg_neg,Real.exp_log hxpos,y,smul_smul,mul_inv_cancel₀ hxpos.ne',one_smul]
  have hex:Real.exp (-s)=‖x‖:=by simp only [s,neg_neg,Real.exp_log hxpos]
  have hhalf:Real.exp (-s/2)=Real.sqrt ‖x‖:=by rw [Real.exp_half,hex]
  have hlocal:ContDiffAt ℝ 2 u (Real.exp (-s) • y):=by
    rw [hxy]
    exact hu.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx)
  have hjet:iteratedFDeriv ℝ 2 (weightedPhysicalDilation s u) y=
      Real.exp (-s/2) • iteratedFDeriv ℝ 2 u x:=by
    change iteratedFDeriv ℝ 2 (Real.exp (3*s/2) • (fun z=>u (Real.exp (-s) • z))) y=_
    have hcomp:ContDiffAt ℝ 2 (fun z:E=>u (Real.exp (-s) • z)) y:=
      hlocal.comp y (contDiffAt_id.const_smul _)
    rw [iteratedFDeriv_const_smul_apply (a:=Real.exp (3*s/2)) hcomp,
      iterated_dilation_of_ne_zero u 2 (Real.exp_pos (-s)).ne',hxy,smul_smul]
    congr 1
    rw [←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    ring
  rw [hjet,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le] at hbnd
  have hbndR:=ENNReal.toReal_mono (ENNReal.mul_ne_top hD hB) hbnd
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)),
    ENNReal.toReal_mul,hhalf] at hbndR
  apply (le_div_iff₀ (Real.sqrt_pos.2 hxpos)).mpr
  nlinarith only [hbndR]

#print axioms exists_weighted_H4_second_jet_decay_constant
end Yamabe3.Analysis.UniformElliptic
