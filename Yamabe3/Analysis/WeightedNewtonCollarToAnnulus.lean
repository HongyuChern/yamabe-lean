import Yamabe3.Analysis.WeightedCollarToAnnulus

/-! The finite dilation cover retains the sharper Newton far-scale decay.
It uses one field and a single bound before scale; no local solutions are
chosen independently on the covering sets. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "W" => nativePolarTimeWindow (Ioo (-(1/4:ℝ)) (1/4))

theorem exists_weighted_Newton_collar_to_annulus_H4_bound :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀(u:E→ℝ) (B:ℝ≥0∞) (T:ℝ),
      (∀t:ℝ,t≤T→MemWkp 4 2 (weightedPhysicalDilation t u) W ∧
        iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation t u) W≤ENNReal.ofReal (Real.exp (5*t/2))*B)→
      ∀s:ℝ,s≤T-1→MemWkp 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ∧
        iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus≤
          C*(ENNReal.ofReal (Real.exp (5*s/2))*B) := by
  let J:={q:((E→ℝ)×ℝ≥0∞)×(ℝ×ℝ) //
    (∀t:ℝ,t≤q.2.1→MemWkp 4 2 (weightedPhysicalDilation t q.1.1) W ∧
      iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation t q.1.1) W≤ENNReal.ofReal (Real.exp (5*t/2))*q.1.2) ∧
      q.2.2≤q.2.1-1}
  let U(j:J):=weightedPhysicalDilation j.val.2.2 j.val.1.1
  let B(j:J):=ENNReal.ofReal (Real.exp (5*j.val.2.2/2))*j.val.1.2
  have hlocal:∀a∈closure halfEndBasicAnnulus,∃(N:Set E) (C:ℝ≥0∞),
      a∈N ∧ IsOpen N ∧ C≠⊤ ∧ ∀j:J,MemWkp 4 2 (U j) N ∧
        iteratedWeakSobolevNorm 4 2 (U j) N≤C*B j:=by
    intro a ha
    have hnorm:(1/2:ℝ)≤‖a‖ ∧ ‖a‖≤2:=by
      have hh:halfEndBasicAnnulus⊆{x:E|(1/2:ℝ)≤‖x‖ ∧ ‖x‖≤2}:=fun x hx=>⟨hx.1.le,hx.2.le⟩
      exact closure_minimal hh ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)) ha
    have ha0:0<‖a‖:=lt_of_lt_of_le (by norm_num) hnorm.1
    let r:=‖a‖⁻¹
    have hr:0<r:=inv_pos.mpr ha0
    have hr2:r≤2:=by
      have he:r*‖a‖=1:=inv_mul_cancel₀ ha0.ne'
      nlinarith only [he,mul_nonneg hr.le (sub_nonneg.mpr hnorm.1)]
    have hl:Real.log r≤1:=by
      have hh:=Real.log_le_sub_one_of_pos hr
      linarith only [hh,hr2]
    let N:=(fun x:E=>r • x) ⁻¹' W
    have hN:IsOpen N:=(nativePolarTimeWindow_open (1/4)).preimage (continuous_id.const_smul r)
    have haN:a∈N:=by
      have he:‖r • a‖=1:=by rw [norm_smul,Real.norm_of_nonneg hr.le];exact inv_mul_cancel₀ ha0.ne'
      change r • a≠0 ∧ -Real.log ‖r • a‖∈Ioo (-(1/4:ℝ)) (1/4)
      refine ⟨norm_ne_zero_iff.mp (by rw [he];norm_num),?_⟩
      rw [he,Real.log_one]
      norm_num
    obtain ⟨D,hD,hd⟩:=exists_weak_dilation_sobolev_bound (d:=3) 4 hr.ne'
    let c:=Real.exp (-(3*Real.log r/2))
    let e:=Real.exp (5*Real.log r/2)
    refine ⟨N,ENNReal.ofReal c*D*ENNReal.ofReal e,haN,hN,by finiteness,fun j=>?_⟩
    have ht:j.val.2.2+Real.log r≤j.val.2.1:=by linarith only [j.property.2,hl]
    have hj:=j.property.1 (j.val.2.2+Real.log r) ht
    have hc:=memWkp_comp_dilation hr.ne' (nativePolarTimeWindow_open (1/4)) (by norm_num) 4 hj.1
    have hcu:=MemWkp.const_smul (by norm_num:(1:ℝ≥0∞)≤2) hN hc c
    have he:(fun x=>c*weightedPhysicalDilation (j.val.2.2+Real.log r) j.val.1.1 (r • x))=U j:=by
      funext x
      exact weightedPhysicalDilation_shift j.val.1.1 j.val.2.2 hr x
    refine ⟨he ▸ hcu,?_⟩
    rw [←he,wkpNorm_const_smul (by norm_num) hN hc c,Real.enorm_eq_ofReal (Real.exp_pos _).le]
    have hh:=(hd W (nativePolarTimeWindow_open (1/4)) _ hj.1).trans
      (mul_le_mul le_rfl hj.2 zero_le zero_le)
    have hexp:ENNReal.ofReal (Real.exp (5*(j.val.2.2+Real.log r)/2))=
        ENNReal.ofReal e*ENNReal.ofReal (Real.exp (5*j.val.2.2/2)):=by
      rw [show 5*(j.val.2.2+Real.log r)/2=5*Real.log r/2+5*j.val.2.2/2 by ring,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact (mul_le_mul le_rfl hh zero_le zero_le).trans_eq (by rw [hexp];dsimp only [B];ring)
  obtain ⟨C,hC,hb⟩:=exists_compact_family_sobolev_bound 4 halfEndBasicAnnulus_isOpen
    (by
      apply Metric.isCompact_of_isClosed_isBounded isClosed_closure
      apply Bornology.IsBounded.closure
      exact (Metric.isBounded_ball (x:=(0:E)) (r:=2)).subset (fun x hx=>by simpa using hx.2)) U B hlocal
  exact ⟨C,hC,fun u B T hu s hs=>hb ⟨((u,B),(T,s)),⟨hu,hs⟩⟩⟩

#print axioms exists_weighted_Newton_collar_to_annulus_H4_bound
end Yamabe3.Analysis.UniformElliptic
