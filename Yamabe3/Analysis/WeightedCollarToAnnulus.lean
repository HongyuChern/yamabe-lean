import Yamabe3.Analysis.FiniteWeightedDilation
import Yamabe3.Analysis.CompactFamilySobolevBound
import Yamabe3.Analysis.NativePolarCollarGeometry

/-! Fixed local annular estimates for one weighted field control its
whole basic annulus. The finite cover rescales the same function, with
exact weights; no different local solutions are patched together. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "W" => nativePolarTimeWindow (Ioo (-(1/4:ℝ)) (1/4))

theorem weightedPhysicalDilation_shift (u : E→ℝ) (s : ℝ) {r : ℝ} (hr : 0<r) (x : E) :
    Real.exp (-(3*Real.log r/2))*weightedPhysicalDilation (s+Real.log r) u (r • x)=
      weightedPhysicalDilation s u x := by
  have he : Real.exp (-(s+Real.log r))*r=Real.exp (-s) := by
    rw [neg_add,Real.exp_add,Real.exp_neg (Real.log r),Real.exp_log hr]
    field_simp
  simp only [weightedPhysicalDilation,smul_smul,he]
  rw [←mul_assoc,←Real.exp_add]
  congr 2
  ring

theorem exists_weighted_collar_to_annulus_H4_bound :
    ∃C : ℝ≥0∞,C≠⊤ ∧ ∀(u : E→ℝ) (B : ℝ≥0∞),
      (∀t : ℝ,Real.log 2+1 ≤ t → MemWkp 4 2 (weightedPhysicalDilation t u) W ∧
        iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation t u) W ≤ B) →
      ∀s : ℝ,4 ≤ s → MemWkp 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ∧
        iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ≤ C*B := by
  let J := {q : (E→ℝ)×ℝ≥0∞ // ∀t : ℝ,Real.log 2+1 ≤ t →
    MemWkp 4 2 (weightedPhysicalDilation t q.1) W ∧
      iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation t q.1) W ≤ q.2} × {s : ℝ // 4 ≤ s}
  let U (j : J) := weightedPhysicalDilation j.2.1 j.1.1.1
  let B (j : J) := j.1.1.2
  have hlocal : ∀a∈closure halfEndBasicAnnulus,∃(N : Set E) (C : ℝ≥0∞),
      a∈N ∧ IsOpen N ∧ C≠⊤ ∧ ∀j : J,MemWkp 4 2 (U j) N ∧
        iteratedWeakSobolevNorm 4 2 (U j) N ≤ C*B j := by
    intro a ha
    have hnorm : (1/2:ℝ) ≤ ‖a‖ ∧ ‖a‖ ≤ 2 := by
      have hh : halfEndBasicAnnulus ⊆ {x : E | (1/2:ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2} := fun x hx => ⟨hx.1.le,hx.2.le⟩
      exact closure_minimal hh ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)) ha
    have ha0 : 0<‖a‖ := lt_of_lt_of_le (by norm_num) hnorm.1
    let r := ‖a‖⁻¹
    have hr : 0<r := inv_pos.mpr ha0
    let N := (fun x : E => r • x) ⁻¹' W
    have hN : IsOpen N := (nativePolarTimeWindow_open (1/4)).preimage (continuous_id.const_smul r)
    have haN : a∈N := by
      have he : ‖r • a‖=1 := by rw [norm_smul,Real.norm_of_nonneg hr.le];exact inv_mul_cancel₀ ha0.ne'
      change r • a≠0 ∧ -Real.log ‖r • a‖∈Ioo (-(1/4:ℝ)) (1/4)
      refine ⟨norm_ne_zero_iff.mp (by rw [he];norm_num),?_⟩
      rw [he,Real.log_one]
      norm_num
    obtain ⟨D,hD,hd⟩ := exists_weak_dilation_sobolev_bound (d:=3) 4 hr.ne'
    let c := Real.exp (-(3*Real.log r/2))
    refine ⟨N,ENNReal.ofReal c*D,haN,hN,by finiteness,?_⟩
    intro j
    have ht : Real.log 2+1 ≤ j.2.1+Real.log r := by
      have hl : Real.log ‖a‖ ≤ Real.log 2 := Real.log_le_log ha0 hnorm.2
      have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
      dsimp only [r]
      rw [Real.log_inv]
      linarith [j.2.2]
    have hj := j.1.2 (j.2.1+Real.log r) ht
    have hc := memWkp_comp_dilation hr.ne' (nativePolarTimeWindow_open (1/4)) (by norm_num) 4 hj.1
    have hcu := MemWkp.const_smul (by norm_num : (1:ℝ≥0∞) ≤ 2) hN hc c
    have he : (fun x => c*weightedPhysicalDilation (j.2.1+Real.log r) j.1.1.1 (r • x))=U j := by
      funext x
      exact weightedPhysicalDilation_shift j.1.1.1 j.2.1 hr x
    refine ⟨he ▸ hcu,?_⟩
    rw [←he,wkpNorm_const_smul (by norm_num) hN hc c,Real.enorm_eq_ofReal (Real.exp_pos _).le]
    exact ((mul_le_mul le_rfl ((hd W (nativePolarTimeWindow_open (1/4)) _ hj.1).trans
      (mul_le_mul le_rfl hj.2 zero_le zero_le)) zero_le zero_le).trans_eq (mul_assoc _ _ _).symm)
  obtain ⟨C,hC,hb⟩ := exists_compact_family_sobolev_bound 4 halfEndBasicAnnulus_isOpen
    (by
      apply Metric.isCompact_of_isClosed_isBounded isClosed_closure
      apply Bornology.IsBounded.closure
      exact (Metric.isBounded_ball (x := (0:E)) (r := 2)).subset (fun x hx => by simpa using hx.2)) U B hlocal
  exact ⟨C,hC,fun u B hu s hs => hb (⟨(u,B),hu⟩,⟨s,hs⟩)⟩

#print axioms weightedPhysicalDilation_shift
#print axioms exists_weighted_collar_to_annulus_H4_bound
end Yamabe3.Analysis.UniformElliptic
