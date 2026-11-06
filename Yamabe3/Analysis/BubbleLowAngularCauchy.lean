import Yamabe3.Analysis.BubbleLowCauchySolver

/-! Assemble the scalar producers on the actual finite low spectral
space. One original AngularL2 source and one pair of original AngularL2
Cauchy data supply every coordinate; no unrelated source is introduced. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

def bubbleSourceCoordinate (H:ℝ →ᵇ AngularL2) (i:AngularIndex):ℝ →ᵇ ℝ:=
  (innerSL ℝ (angularBasis i)).compLeftContinuousBounded ℝ H

@[simp] theorem bubbleSourceCoordinate_apply (H:ℝ →ᵇ AngularL2) (i:AngularIndex) (s:ℝ):
    bubbleSourceCoordinate H i s=inner ℝ (angularBasis i) (H s):=rfl

def bubbleLowAngularCurve (q:AngularIndex→ℝ→ℝ) (t:ℝ):AngularL2:=
  ∑i∈nativeLowIndexFinset,q i t • angularBasis i

theorem bubbleLowAngularCurve_hasDerivAt (q:AngularIndex→ℝ→ℝ)
    (hq:∀i∈nativeLowIndexFinset,ContDiff ℝ 2 (q i)) (t:ℝ):
    HasDerivAt (bubbleLowAngularCurve q)
      (∑i∈nativeLowIndexFinset,deriv (q i) t • angularBasis i) t:=by
  exact HasDerivAt.fun_sum fun i hi=>(hq i hi).differentiable (by norm_num) t |>.hasDerivAt.smul_const _

theorem exists_actual_angular_low_cauchy_solver (H:ℝ →ᵇ AngularL2)
    {t₀:ℝ} (ht:0<t₀) (d n:AngularL2):
    ∃(c:AngularIndex→ℝ) (q:AngularIndex→ℝ→ℝ),
      (∀i∈nativeLowIndexFinset,
        c i=bubbleLowCauchyCompensation i t₀ (inner ℝ (angularBasis i) d)
          (inner ℝ (angularBasis i) n) (bubbleLowSourceMoment i (bubbleSourceCoordinate H i) t₀) ∧
        ContDiff ℝ 2 (q i) ∧
        (∀t,deriv (deriv (q i)) t-bubbleLowCoefficient i t*q i t=
          -(Real.exp (2*t)*inner ℝ (angularBasis i) (H (-t))+c i*bubbleCompensation i t)) ∧
        q i t₀=inner ℝ (angularBasis i) d ∧
        deriv (q i) t₀=inner ℝ (angularBasis i) n ∧
        Tendsto (q i) atBot (𝓝 0) ∧ Tendsto (deriv (q i)) atBot (𝓝 0)) ∧
      bubbleLowAngularCurve q t₀=nativeLowProjection d ∧
      HasDerivAt (bubbleLowAngularCurve q) (nativeLowProjection n) t₀:=by
  classical
  have hs (i:{i:AngularIndex // i∈nativeLowIndexFinset}):=
    exists_actual_bubble_low_cauchy_solver i.val i.property (bubbleSourceCoordinate H i.val) ht
      (inner ℝ (angularBasis i.val) d) (inner ℝ (angularBasis i.val) n)
  choose c q hh using hs
  let C:AngularIndex→ℝ:=fun i=>if hi:i∈nativeLowIndexFinset then c ⟨i,hi⟩ else 0
  let Q:AngularIndex→ℝ→ℝ:=fun i=>if hi:i∈nativeLowIndexFinset then q ⟨i,hi⟩ else fun _=>0
  have hQ (i:AngularIndex) (hi:i∈nativeLowIndexFinset):Q i=q ⟨i,hi⟩:=by simp only [Q,dif_pos hi]
  have hC (i:AngularIndex) (hi:i∈nativeLowIndexFinset):C i=c ⟨i,hi⟩:=by simp only [C,dif_pos hi]
  have hQC:∀i∈nativeLowIndexFinset,ContDiff ℝ 2 (Q i):=fun i hi=>by rw [hQ i hi];exact (hh ⟨i,hi⟩).2.1
  refine ⟨C,Q,?_,?_,?_⟩
  · intro i hi
    rw [hQ i hi,hC i hi]
    simpa only [bubbleSourceCoordinate_apply] using hh ⟨i,hi⟩
  · rw [bubbleLowAngularCurve,nativeLowProjection_eq_finite]
    change (∑i∈nativeLowIndexFinset,Q i t₀ • angularBasis i)=
      ∑i∈nativeLowIndexFinset,inner ℝ (angularBasis i) d • angularBasis i
    apply Finset.sum_congr rfl
    intro i hi
    rw [hQ i hi,(hh ⟨i,hi⟩).2.2.2.1]
  · have he:(∑i∈nativeLowIndexFinset,deriv (Q i) t₀ • angularBasis i)=nativeLowProjection n:=by
      rw [nativeLowProjection_eq_finite]
      change _=∑i∈nativeLowIndexFinset,inner ℝ (angularBasis i) n • angularBasis i
      apply Finset.sum_congr rfl
      intro i hi
      rw [hQ i hi,(hh ⟨i,hi⟩).2.2.2.2.1]
    exact (bubbleLowAngularCurve_hasDerivAt Q hQC t₀).congr_deriv he

#print axioms bubbleLowAngularCurve_hasDerivAt
#print axioms exists_actual_angular_low_cauchy_solver
end Yamabe3.Analysis.Delaunay
