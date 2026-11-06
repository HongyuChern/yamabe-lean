import Yamabe3.Analysis.NativeLowGlobalL2
import Yamabe3.Analysis.NativeFiniteDecayingGradient

/-! The actual retained finite entrance lift has its own smooth physical
weak equation and genuine global L2 right-hand side. The lift is not
silently given zero boundary data. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SpherePolar SphereSpectrum UniformElliptic
open Poincare.Analysis.Sobolev.Weak
local notation "O" => Metric.ball (0:E) 1 \ {(0:E)}

def nativeFiniteStationaryCylinder (s:Finset AngularIndex) (c:AngularIndex→ℝ) : CylinderSource :=
  let H:C(S,ℝ):=∑i∈s,c i • nativeAngularRepresentativeMap i
  BoundedContinuousFunction.ofNormedAddCommGroup (fun p:ℝ × S=>H p.2)
    (H.continuous.comp continuous_snd) ‖H‖ (fun p=>ContinuousMap.norm_coe_le_norm H p.2)

theorem nativeFiniteStationaryCylinder_apply (s:Finset AngularIndex) (c:AngularIndex→ℝ)
    (p:ℝ × S) : nativeFiniteStationaryCylinder s c p=∑i∈s,c i*angularRepresentative i p.2 := by
  simp [nativeFiniteStationaryCylinder,nativeAngularRepresentativeMap]

variable (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0≤v t ∧ v t≤1) (F:ℝ →ᵇ AngularL2)

def nativeLowEntranceSourceCylinder : CylinderSource :=
  nativeFiniteStationaryCylinder nativeLowIndexFinset
    (fun i=>(15/4-angularEigenvalue i)*inner ℝ (angularBasis i) (nativeLowSolvedCurve v hv hb F 0))

def nativeLowEntranceRHS (x:E) : ℝ :=
  physicalForcing (fun p:ℝ × S=>Real.exp (-2*p.1)*nativeLowEntranceSourceCylinder v hv hb F p) x/8

theorem nativeLowEntranceCoefficient_second (i:AngularIndex) (t:ℝ) :
    deriv (deriv (nativeLowEntranceCoefficient v hv hb F i)) t=
      4*nativeLowEntranceCoefficient v hv hb F i t := by
  have hfun:deriv (nativeLowEntranceCoefficient v hv hb F i)=
      fun s=> -2*nativeLowEntranceCoefficient v hv hb F i s :=
    funext (nativeLowEntranceCoefficient_deriv v hv hb F i)
  rw [hfun]
  have hd:=((nativeLowEntranceCoefficient_smooth v hv hb F i).differentiable (by simp) t).hasDerivAt.const_mul (-2)
  rw [hd.deriv,nativeLowEntranceCoefficient_deriv]
  unfold nativeLowEntranceCoefficient
  ring

theorem nativeLowEntranceLift_smooth : ContDiffOn ℝ ∞ (nativeLowEntranceLift v hv hb F) ({(0:E)}ᶜ) := by
  intro x hx
  exact (contDiffAt_finitePhysical nativeLowIndexFinset (nativeLowEntranceCoefficient v hv hb F)
    (fun i _=>nativeLowEntranceCoefficient_smooth v hv hb F i) hx).contDiffWithinAt

theorem nativeLowEntranceRHS_memLp : MemLp (nativeLowEntranceRHS v hv hb F) 2 (volume.restrict O) := by
  change MemLp (fun x=>physicalForcing (fun p:ℝ × S=>Real.exp (-2*p.1)*
    nativeLowEntranceSourceCylinder v hv hb F p) x/8) 2 (volume.restrict O)
  simpa only [div_eq_mul_inv] using
    (nativeCylinderSource_physical_memLp (nativeLowEntranceSourceCylinder v hv hb F)).mul_const (8:ℝ)⁻¹

theorem nativeLowEntranceLift_weak_equation :
    ∀φ:E→ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆O →
      (∫x in O,∑j:Fin 3, fderiv ℝ (nativeLowEntranceLift v hv hb F) x (EuclideanSpace.single j 1)*
        fderiv ℝ φ x (EuclideanSpace.single j 1))=
      ∫x in O,nativeLowEntranceRHS v hv hb F x*φ x := by
  let q:=nativeLowEntranceCoefficient v hv hb F
  let c:AngularIndex→ℝ:=fun i=>inner ℝ (angularBasis i) (nativeLowSolvedCurve v hv hb F 0)
  let z:AngularIndex→ℝ→ℝ:=fun i t=>(15/4-angularEigenvalue i)*q i t
  have hq (i:AngularIndex) : ContDiff ℝ 2 (q i):=
    (nativeLowEntranceCoefficient_smooth v hv hb F i).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hode (i:AngularIndex) (t:ℝ) : deriv (deriv (q i)) t=(angularEigenvalue i+1/4-0)*q i t+z i t := by
    rw [nativeLowEntranceCoefficient_second]
    dsimp only [z]
    ring
  have hz:finiteAngular nativeLowIndexFinset z=
      fun p:ℝ × S=>Real.exp (-2*p.1)*nativeLowEntranceSourceCylinder v hv hb F p := by
    funext p
    rw [nativeLowEntranceSourceCylinder,nativeFiniteStationaryCylinder_apply,Finset.mul_sum]
    change (∑i∈nativeLowIndexFinset,((15/4-angularEigenvalue i)*
      (Real.exp (-2*p.1)*c i))*angularRepresentative i p.2)=_
    apply Finset.sum_congr rfl
    intro i hi
    ring
  intro φ hφ hc hs
  have hh:=native_finite_c2_physical_weak_equation (Metric.isOpen_ball.sdiff isClosed_singleton)
    (fun x hx=>⟨by simpa using hx.2,by simpa using hx.1⟩)
    (fun _:ℝ=>0) nativeLowIndexFinset q z
    (fun i _=>(hq i).contDiffOn) (fun i _ t _=>hode i t) φ hφ hc hs
  rw [hz] at hh
  change (∫x in O,∑j:Fin 3,fderiv ℝ (finitePhysical nativeLowIndexFinset q) x (EuclideanSpace.single j 1)*
    fderiv ℝ φ x (EuclideanSpace.single j 1))=
    ∫x in O,physicalForcing (fun p:ℝ × S=>Real.exp (-2*p.1)*nativeLowEntranceSourceCylinder v hv hb F p) x/8*φ x
  simpa only [zero_div,zero_mul,add_zero] using hh

theorem nativeLowEntranceLift_H1_gradient : MemH1 (nativeLowEntranceLift v hv hb F) O ∧
    ∀j:Fin 3,MemLp (fun x=>fderiv ℝ (nativeLowEntranceLift v hv hb F) x (EuclideanSpace.single j 1))
      2 (volume.restrict O) := by
  have hq (i:AngularIndex) : ContDiff ℝ 2 (nativeLowEntranceCoefficient v hv hb F i):=
    (nativeLowEntranceCoefficient_smooth v hv hb F i).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have h0 (i:AngularIndex) (t:ℝ) : ‖nativeLowEntranceCoefficient v hv hb F i t‖≤(2*‖F‖)*Real.exp (-2*t):=by
    rw [nativeLowEntranceCoefficient,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_mul_of_nonneg_left (nativeLowSolvedCurve_coordinate_bounds v hv hb F i 0).1
      (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  have h1 (i:AngularIndex) (t:ℝ) : ‖deriv (nativeLowEntranceCoefficient v hv hb F i) t‖≤(4*‖F‖)*Real.exp (-2*t):=by
    rw [nativeLowEntranceCoefficient_deriv,norm_mul]
    change ‖(-2:ℝ)‖*‖nativeLowEntranceCoefficient v hv hb F i t‖≤_
    norm_num only [norm_neg,Real.norm_ofNat]
    linarith [h0 i t]
  exact ⟨(finitePhysical_H1_of_exp_decay nativeLowIndexFinset _ (fun i _=>hq i)
    (by positivity) (by positivity) (fun i _ t _=>h0 i t) (fun i _ t _=>h1 i t)).1,
    (finitePhysical_gradient_L2_of_exp_decay nativeLowIndexFinset _ (fun i _=>hq i)
      (by positivity) (by positivity) (fun i _ t _=>h0 i t) (fun i _ t _=>h1 i t)).1⟩

#print axioms nativeFiniteStationaryCylinder_apply
#print axioms nativeLowEntranceCoefficient_second
#print axioms nativeLowEntranceLift_smooth
#print axioms nativeLowEntranceRHS_memLp
#print axioms nativeLowEntranceLift_weak_equation
#print axioms nativeLowEntranceLift_H1_gradient
end Yamabe3.Analysis.Delaunay
