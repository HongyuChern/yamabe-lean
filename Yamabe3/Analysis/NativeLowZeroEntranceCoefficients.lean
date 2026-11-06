import Yamabe3.Analysis.NativeLowCurveJets

/-! The actual low entrance is removed by a specified decaying finite
lifting. This does not set the original low boundary value to zero. Both
the lifting and the remaining zero-entrance field keep the same source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.SphereSpectrum

def nativeLowEntranceCoefficient (v:ℝ→ℝ) (hv:Continuous v)
    (hb:∀t,0≤v t ∧ v t≤1) (F:ℝ →ᵇ AngularL2) (i:AngularIndex) (t:ℝ) : ℝ :=
  Real.exp (-2*t)*inner ℝ (angularBasis i) (nativeLowSolvedCurve v hv hb F 0)

def nativeLowZeroEntranceCoefficient (v:ℝ→ℝ) (hv:Continuous v)
    (hb:∀t,0≤v t ∧ v t≤1) (F:ℝ →ᵇ AngularL2) (i:AngularIndex) (t:ℝ) : ℝ :=
  nativeLowPhysicalCoefficient v hv hb F i t-nativeLowEntranceCoefficient v hv hb F i t

theorem nativeLowPhysicalCoefficient_deriv (v:ℝ→ℝ) (hv:Continuous v)
    (hb:∀t,0≤v t ∧ v t≤1) (F:ℝ →ᵇ AngularL2) (i:AngularIndex) (t:ℝ) :
    deriv (nativeLowPhysicalCoefficient v hv hb F i) t = Real.exp (-2*t)*
      (-2*inner ℝ (angularBasis i) (nativeLowSolvedCurve v hv hb F t)+
        deriv (fun s=>inner ℝ (angularBasis i) (nativeLowSolvedCurve v hv hb F s)) t) := by
  have hq := nativeLowAngularInverseCLM_coefficient_C2 v hv hb (k:=2) (by norm_num)
    (by norm_num) (nativeLowSource F) (nativeLowSource_high_zero F) i
  have he := (((hasDerivAt_id t).const_mul (-2)).exp).mul
    ((hq.differentiable (by norm_num) t).hasDerivAt)
  change HasDerivAt (nativeLowPhysicalCoefficient v hv hb F i) _ t at he
  rw [he.deriv]
  simp only [id_eq,nativeLowSolvedCurve]
  ring

theorem nativeLowPhysicalCoefficient_bounds (v:ℝ→ℝ) (hv:Continuous v)
    (hb:∀t,0≤v t ∧ v t≤1) (F:ℝ →ᵇ AngularL2) (i:AngularIndex) (t:ℝ) :
    ‖nativeLowPhysicalCoefficient v hv hb F i t‖≤(2*‖F‖)*Real.exp (-2*t) ∧
    ‖deriv (nativeLowPhysicalCoefficient v hv hb F i) t‖≤(12*‖F‖)*Real.exp (-2*t) := by
  have h := nativeLowSolvedCurve_coordinate_bounds v hv hb F i t
  dsimp only at h
  constructor
  · rw [nativeLowPhysicalCoefficient,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_mul_of_nonneg_left h.1 (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  · rw [nativeLowPhysicalCoefficient_deriv,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
    have hh : ‖-2*inner ℝ (angularBasis i) (nativeLowSolvedCurve v hv hb F t)+
        deriv (fun s=>inner ℝ (angularBasis i) (nativeLowSolvedCurve v hv hb F s)) t‖≤12*‖F‖ := by
      apply (norm_add_le _ _).trans
      rw [norm_mul]
      norm_num only [norm_neg,Real.norm_ofNat]
      linarith [h.1,h.2.1]
    exact (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le).trans_eq (mul_comm _ _)

theorem nativeLowEntranceCoefficient_smooth (v:ℝ→ℝ) (hv:Continuous v)
    (hb:∀t,0≤v t ∧ v t≤1) (F:ℝ →ᵇ AngularL2) (i:AngularIndex) :
    ContDiff ℝ ∞ (nativeLowEntranceCoefficient v hv hb F i) := by
  unfold nativeLowEntranceCoefficient
  fun_prop

theorem nativeLowEntranceCoefficient_deriv (v:ℝ→ℝ) (hv:Continuous v)
    (hb:∀t,0≤v t ∧ v t≤1) (F:ℝ →ᵇ AngularL2) (i:AngularIndex) (t:ℝ) :
    deriv (nativeLowEntranceCoefficient v hv hb F i) t =
      -2*(Real.exp (-2*t)*inner ℝ (angularBasis i) (nativeLowSolvedCurve v hv hb F 0)) := by
  have h := ((((hasDerivAt_id t).const_mul (-2)).exp).mul_const
    (inner ℝ (angularBasis i) (nativeLowSolvedCurve v hv hb F 0))).deriv
  change deriv (nativeLowEntranceCoefficient v hv hb F i) t = _ at h
  rw [h]
  simp only [id_eq]
  ring

theorem nativeLowZeroEntranceCoefficient_C2_zero_bounds (v:ℝ→ℝ) (hv:Continuous v)
    (hb:∀t,0≤v t ∧ v t≤1) (F:ℝ →ᵇ AngularL2) (i:AngularIndex) :
    ContDiff ℝ 2 (nativeLowZeroEntranceCoefficient v hv hb F i) ∧
    nativeLowZeroEntranceCoefficient v hv hb F i 0=0 ∧
    ∀t, ‖nativeLowZeroEntranceCoefficient v hv hb F i t‖≤(4*‖F‖)*Real.exp (-2*t) ∧
      ‖deriv (nativeLowZeroEntranceCoefficient v hv hb F i) t‖≤(16*‖F‖)*Real.exp (-2*t) := by
  have hq := (nativeLowPhysicalCoefficient_C2_equation v hv hb F i).1
  have hp := nativeLowEntranceCoefficient_smooth v hv hb F i
  have hC : ContDiff ℝ 2 (nativeLowZeroEntranceCoefficient v hv hb F i) :=
    hq.sub (hp.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  refine ⟨hC,by simp [nativeLowZeroEntranceCoefficient,nativeLowPhysicalCoefficient,nativeLowEntranceCoefficient],?_⟩
  intro t
  have hqb := nativeLowPhysicalCoefficient_bounds v hv hb F i t
  have h0 := (nativeLowSolvedCurve_coordinate_bounds v hv hb F i 0).1
  have hp0 : ‖nativeLowEntranceCoefficient v hv hb F i t‖≤(2*‖F‖)*Real.exp (-2*t) := by
    rw [nativeLowEntranceCoefficient,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_mul_of_nonneg_left h0 (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  have hp1 : ‖deriv (nativeLowEntranceCoefficient v hv hb F i) t‖≤(4*‖F‖)*Real.exp (-2*t) := by
    rw [nativeLowEntranceCoefficient_deriv,norm_mul]
    change ‖(-2:ℝ)‖*‖nativeLowEntranceCoefficient v hv hb F i t‖≤_
    norm_num only [norm_neg,Real.norm_ofNat]
    linarith
  constructor
  · change ‖nativeLowPhysicalCoefficient v hv hb F i t-nativeLowEntranceCoefficient v hv hb F i t‖≤_
    apply (norm_sub_le _ _).trans
    linarith [hqb.1]
  · have he : deriv (nativeLowZeroEntranceCoefficient v hv hb F i) t =
        deriv (nativeLowPhysicalCoefficient v hv hb F i) t-deriv (nativeLowEntranceCoefficient v hv hb F i) t :=
      ((hq.differentiable (by norm_num) t).hasDerivAt.sub (hp.differentiable (by simp) t).hasDerivAt).deriv
    rw [he]
    apply (norm_sub_le _ _).trans
    linarith [hqb.2]

#print axioms nativeLowPhysicalCoefficient_deriv
#print axioms nativeLowPhysicalCoefficient_bounds
#print axioms nativeLowEntranceCoefficient_smooth
#print axioms nativeLowZeroEntranceCoefficient_C2_zero_bounds
end Yamabe3.Analysis.Delaunay
