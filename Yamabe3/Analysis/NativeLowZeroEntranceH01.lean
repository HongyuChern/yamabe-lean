import Yamabe3.Analysis.NativeLowZeroEntranceCoefficients
import Yamabe3.Analysis.NativeFiniteDecayingH1
import Yamabe3.Analysis.NativeDecayingZeroEntranceH01

/-! The actual low field minus its actual entrance lifting belongs to
MemH01 on the punctured unit ball. Its approximating witnesses are proved
by physical cutoff estimates; zero trace is not an input. The original
low field and its nonzero entrance remain separate objects. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold Topology ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.SphereSpectrum Yamabe3.Analysis.SpherePolar
open Poincare.Analysis.Sobolev.Weak

def nativeLowZeroEntranceField (v:ℝ→ℝ) (hv:Continuous v)
    (hb:∀t,0≤v t ∧ v t≤1) (F:ℝ →ᵇ AngularL2) : E→ℝ :=
  finitePhysical nativeLowIndexFinset (nativeLowZeroEntranceCoefficient v hv hb F)

def nativeLowEntranceLift (v:ℝ→ℝ) (hv:Continuous v)
    (hb:∀t,0≤v t ∧ v t≤1) (F:ℝ →ᵇ AngularL2) : E→ℝ :=
  finitePhysical nativeLowIndexFinset (nativeLowEntranceCoefficient v hv hb F)

theorem nativeLowZeroEntranceField_H1 (v:ℝ→ℝ) (hv:Continuous v)
    (hb:∀t,0≤v t ∧ v t≤1) (F:ℝ →ᵇ AngularL2) :
    MemH1 (nativeLowZeroEntranceField v hv hb F) (Metric.ball (0:E) 1 \ {(0:E)}) := by
  exact (finitePhysical_H1_of_exp_decay nativeLowIndexFinset
    (nativeLowZeroEntranceCoefficient v hv hb F)
    (fun i _=>(nativeLowZeroEntranceCoefficient_C2_zero_bounds v hv hb F i).1)
    (A:=4*‖F‖) (B:=16*‖F‖) (by positivity) (by positivity)
    (fun i _ t _=>(nativeLowZeroEntranceCoefficient_C2_zero_bounds v hv hb F i).2.2 t |>.1)
    (fun i _ t _=>(nativeLowZeroEntranceCoefficient_C2_zero_bounds v hv hb F i).2.2 t |>.2)).1

theorem nativeLowZeroEntranceField_H01 (v:ℝ→ℝ) (hv:Continuous v)
    (hb:∀t,0≤v t ∧ v t≤1) (F:ℝ →ᵇ AngularL2) :
    MemH01 (nativeLowZeroEntranceField v hv hb F) (Metric.ball (0:E) 1 \ {(0:E)}) := by
  classical
  let s:=nativeLowIndexFinset
  let q:=nativeLowZeroEntranceCoefficient v hv hb F
  let U:ℝ→AngularL2:=fun t=>∑i∈s, q i t • angularBasis i
  have hq (i:AngularIndex) : ContDiff ℝ 2 (q i) ∧ q i 0=0 ∧
      ∀t,‖q i t‖≤(4*‖F‖)*Real.exp (-2*t) ∧ ‖deriv (q i) t‖≤(16*‖F‖)*Real.exp (-2*t) :=
    nativeLowZeroEntranceCoefficient_C2_zero_bounds v hv hb F i
  have hU : Continuous U:=continuous_finsetSum _ (fun i _=>(hq i).1.continuous.smul continuous_const)
  have hw : Continuous (finiteAngular s q) := by
    apply continuous_finsetSum
    intro i hi
    exact ((hq i).1.continuous.comp continuous_fst).mul
      ((smooth_angularRepresentative i).continuous.comp continuous_snd)
  have hUnorm (t:ℝ) : ‖U t‖≤Real.exp (-2*t)*((s.card:ℝ)*(4*‖F‖)) := by
    calc
      _ ≤ ∑i∈s,‖q i t • angularBasis i‖ := norm_sum_le _ _
      _ ≤ ∑i∈s,(4*‖F‖)*Real.exp (-2*t) := Finset.sum_le_sum (fun i hi=>by
        rw [norm_smul,angularBasis.orthonormal.norm_eq_one i,mul_one]
        exact ((hq i).2.2 t).1)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  let D:ℝ→AngularL2:=fun t=>∑i∈s, deriv (q i) t • angularBasis i
  have hD (t:ℝ) : HasDerivAt U (D t) t := by
    apply HasDerivAt.fun_sum
    intro i _
    exact ((hq i).1.differentiable (by norm_num) t).hasDerivAt.smul_const (angularBasis i)
  have hDnorm (t:ℝ) (ht:0≤t) : ‖D t‖≤(s.card:ℝ)*(16*‖F‖) := by
    have he:Real.exp (-2*t)≤1:=Real.exp_le_one_iff.mpr (by linarith)
    calc
      _ ≤ ∑i∈s,‖deriv (q i) t • angularBasis i‖ := norm_sum_le _ _
      _ ≤ ∑i∈s,16*‖F‖ := Finset.sum_le_sum (fun i hi=>by
        rw [norm_smul,angularBasis.orthonormal.norm_eq_one i,mul_one]
        exact (((hq i).2.2 t).2).trans (by nlinarith [norm_nonneg F]))
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  have hU0:U 0=0:=by simp only [U,fun i=>(hq i).2.1,zero_smul,Finset.sum_const_zero]
  have hlinear (t:ℝ) (ht:0≤t) : ‖U t‖≤((s.card:ℝ)*(16*‖F‖))*t := by
    have hh:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f:=U) (f':=D) (s:=Ici (0:ℝ)) (C:=(s.card:ℝ)*(16*‖F‖)) (x:=0) (y:=t)
      (fun r _=>(hD r).hasDerivWithinAt) hDnorm (convex_Ici (0:ℝ)) (by simp) ht
    simpa only [hU0,sub_zero,Real.norm_of_nonneg ht] using hh
  have hh:=native_memH01_of_decaying_zero_entrance_lift hU hw.measurable (finiteAngular_ae s q)
    (by simpa only [←finitePhysical_eq_lift,nativeLowZeroEntranceField,s,q] using nativeLowZeroEntranceField_H1 v hv hb F)
    ((s.card:ℝ)*(4*‖F‖)) ((s.card:ℝ)*(16*‖F‖)) hUnorm hlinear
  simpa only [←finitePhysical_eq_lift,nativeLowZeroEntranceField,s,q] using hh

theorem nativeLowPhysicalField_split_entrance (v:ℝ→ℝ) (hv:Continuous v)
    (hb:∀t,0≤v t ∧ v t≤1) (F:ℝ →ᵇ AngularL2) (x:E) :
    nativeLowZeroEntranceField v hv hb F x+nativeLowEntranceLift v hv hb F x=
      nativeLowPhysicalField v hv hb F x := by
  by_cases hx:x=0
  · simp [hx,nativeLowZeroEntranceField,nativeLowEntranceLift,nativeLowPhysicalField,
      finitePhysical_eq_lift,cylinderLift_zero]
  let y:puncturedSpace:=⟨x,hx⟩
  change finitePhysical nativeLowIndexFinset (nativeLowZeroEntranceCoefficient v hv hb F) (y:E)+
    finitePhysical nativeLowIndexFinset (nativeLowEntranceCoefficient v hv hb F) (y:E)=
    finitePhysical nativeLowIndexFinset (nativeLowPhysicalCoefficient v hv hb F) (y:E)
  simp only [finitePhysical_eq_lift,cylinderLift_coe,puncturedCylinderLift,finiteAngular,
    nativeLowZeroEntranceCoefficient]
  simp_rw [sub_mul,Finset.sum_sub_distrib]
  ring

#print axioms nativeLowZeroEntranceField_H1
#print axioms nativeLowZeroEntranceField_H01
#print axioms nativeLowPhysicalField_split_entrance
end Yamabe3.Analysis.Delaunay
