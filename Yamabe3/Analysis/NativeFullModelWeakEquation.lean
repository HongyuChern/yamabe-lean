import Yamabe3.Analysis.NativeLowGlobalL2
import Yamabe3.Analysis.NativeFiniteDecayingGradient
import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndL2Equation
import PoincareLib.Analysis.Elliptic.Regularity.Iteration.WeakEquation

/-! One actual weak equation for the sum of the high and low fields of
the same full source. All source projections cancel back to the original
source pointwise. This is not a high-H2 projection assumption. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration
local notation "O" => Metric.ball (0:E) 1 \ {(0:E)}

theorem nativeWeakEquation_add {Ω:Set E} {P R:Fin 3→E→ℝ} {g h:E→ℝ}
    (hP:∀i,MemLp (P i) 2 (volume.restrict Ω))
    (hR:∀i,MemLp (R i) 2 (volume.restrict Ω))
    (hg:MemLp g 2 (volume.restrict Ω)) (hh:MemLp h 2 (volume.restrict Ω))
    (he:WeakEquation Ω P g) (hf:WeakEquation Ω R h) :
    WeakEquation Ω (fun i x=>P i x+R i x) (fun x=>g x+h x) := by
  intro φ hφ hc hs
  have hφL : MemLp φ 2 (volume.restrict Ω):=(hφ.continuous.memLp_of_hasCompactSupport hc).restrict Ω
  have hd (i:Fin 3) : MemLp (partialDeriv i φ) 2 (volume.restrict Ω):=
    ((contDiff_partial hφ i).continuous.memLp_of_hasCompactSupport
      (hc.fderiv_apply (𝕜:=ℝ) (EuclideanSpace.single i 1))).restrict Ω
  have hPI : Integrable (fun x=>∑i:Fin 3,P i x*partialDeriv i φ x) (volume.restrict Ω):=
    integrable_finsetSum _ (fun i _=>(hP i).integrable_mul (hd i))
  have hRI : Integrable (fun x=>∑i:Fin 3,R i x*partialDeriv i φ x) (volume.restrict Ω):=
    integrable_finsetSum _ (fun i _=>(hR i).integrable_mul (hd i))
  simp_rw [add_mul,Finset.sum_add_distrib]
  have hgI : Integrable (fun x=>g x*φ x) (volume.restrict Ω):=hg.integrable_mul hφL
  have hhI : Integrable (fun x=>h x*φ x) (volume.restrict Ω):=hh.integrable_mul hφL
  rw [integral_add hPI hRI,integral_add hgI hhI,he φ hφ hc hs,hf φ hφ hc hs]

variable {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1) (p:DelaunayPhaseData κ)

theorem fullModelPhysicalField_same_weak_equation (f:HalfEndPhysicalH2SourceGraph) :
    let u:=fullModelPhysicalField hκ0 hκ1 p f
    let F:=halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f)
    let g:=fun x=>F x/8+nativeHalfEndPotentialCoefficient p.potential x*u x
    MemH1 u O ∧ MemLp g 2 (volume.restrict O) ∧
      ∃du:Fin 3→E→ℝ, (∀i,MemLp (du i) 2 (volume.restrict O)) ∧
        (∀i,HasWeakPartialDeriv i (du i) u O) ∧ WeakEquation O du g := by
  let G:=halfEndSourceCylinderCLM (halfEndPhysicalH2SourceGraphValue f)
  let zH:=nativeHighSourceCylinder G
  let F:=halfEndFullSourceAngularCLM f
  let v:ℝ→ℝ:=fun t=>p.orbit (t+p.phase)
  have hv:Continuous v:=p.smooth.continuous.comp (continuous_id.add continuous_const)
  have hb:∀t,0≤v t ∧ v t≤1:=fun t=>p.bounded (t+p.phase)
  let uH:=cylinderLift (fullModelHighJoint hκ0 hκ1 p f)
  let uL:=fullModelLowField p f
  let dL:Fin 3→E→ℝ:=fun i x=>fderiv ℝ uL x (EuclideanSpace.single i 1)
  let fH:=physicalForcing (fun a:ℝ × S=>Real.exp (-2*a.1)*zH a)
  let fL:=physicalForcing (fun a:ℝ × S=>Real.exp (-2*a.1)*nativeLowSourceCylinder F a)
  let gH:=fun x=>fH x/8+nativeHalfEndPotentialCoefficient p.potential x*uH x
  let gL:=fun x=>fL x/8+nativeHalfEndPotentialCoefficient p.potential x*uL x
  have hO:IsOpen O:=Metric.isOpen_ball.sdiff isClosed_singleton
  have hzAE (t:ℝ) : (fun θ=>zH (t,θ)) =ᵐ[angularVolume]
      (nativeHighProjection (halfEndH2SourceToAngularCLM f t.toNNReal):S→ℝ) := by
    have he:=nativeHighSourceCylinder_ae G t
    change (fun θ=>zH (t,θ)) =ᵐ[angularVolume] (nativeHighProjection (halfEndFullSourceAngularCLM f t):S→ℝ) at he
    rw [halfEndFullSourceAngular_toNNReal] at he
    exact he
  obtain ⟨hH1,hgH,-,-,dH,hdH,-,-,heH,-,-,-,-⟩:=
    native_forced_halfEnd_global_quantitative_L2_equation hκ0 hκ1 p.potential p.kernel_bound
      p.potential_nonneg (halfEndH2SourceToAngularCLM f)
      (nativeHalfHighDirichletJoint_measurable hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg _)
      zH.continuous.measurable
      (nativeHalfHighDirichletJoint_ae hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg _) hzAE
  change MemLp gH 2 (volume.restrict O) at hgH
  have hL:MemH1 uL O:=(finitePhysical_H1_of_exp_decay nativeLowIndexFinset
    (nativeLowPhysicalCoefficient v hv hb F)
    (fun i _=>(nativeLowPhysicalCoefficient_C2_equation v hv hb F i).1)
    (A:=2*‖F‖) (B:=12*‖F‖) (by positivity) (by positivity)
    (fun i _ t _=>(nativeLowPhysicalCoefficient_bounds v hv hb F i t).1)
    (fun i _ t _=>(nativeLowPhysicalCoefficient_bounds v hv hb F i t).2)).1
  have hdL:∀i,MemLp (dL i) 2 (volume.restrict O):=
    (finitePhysical_gradient_L2_of_exp_decay nativeLowIndexFinset (nativeLowPhysicalCoefficient v hv hb F)
      (fun i _=>(nativeLowPhysicalCoefficient_C2_equation v hv hb F i).1)
      (A:=2*‖F‖) (B:=12*‖F‖) (by positivity) (by positivity)
      (fun i _ t _=>(nativeLowPhysicalCoefficient_bounds v hv hb F i t).1)
      (fun i _ t _=>(nativeLowPhysicalCoefficient_bounds v hv hb F i t).2)).1
  have hC1:ContDiffOn ℝ 1 uL O:=
    ((nativeLowPhysicalField_C2 v hv hb F).mono (fun x hx=>hx.2)).of_le (by norm_num)
  have hwL:∀i,HasWeakPartialDeriv i (dL i) uL O:=
    fun i=>native_hasWeakPartialDeriv_of_contDiffOn_one hO hC1 i
  have hgL:MemLp gL 2 (volume.restrict O):=by
    have hs:MemLp (fun x=>fL x/8) 2 (volume.restrict O):=by
      simpa only [div_eq_mul_inv] using (nativeCylinderSource_physical_memLp (nativeLowSourceCylinder F)).mul_const (8:ℝ)⁻¹
    exact hs.add (nativeLowPhysicalField_potential_memLp v hv hb F p.potential)
  have heL:WeakEquation O dL gL:=by
    intro φ hφ hc hs
    have hh:=nativeLowPhysicalField_weak_equation v hv hb F hO
      (fun x hx=>⟨by simpa using hx.2,by simpa using hx.1⟩) φ hφ hc hs
    have hfs : finiteAngular nativeLowIndexFinset
        (fun i t=>Real.exp (-2*t)*inner ℝ (angularBasis i) (nativeLowSource F t))=
        fun a:ℝ × S=>Real.exp (-2*a.1)*nativeLowSourceCylinder F a :=
      funext (nativeLowSource_finite_weighted_eq F)
    rw [hfs] at hh
    exact hh
  let wh:MemW1pWitness 2 uH O:=
    ⟨hH1.1,fun x=>WithLp.toLp 2 (fun i=>dH i x),fun i=>Lp.memLp (dH i),hdH⟩
  let wl:MemW1pWitness 2 uL O:=
    ⟨hL.1,fun x=>WithLp.toLp 2 (fun i=>dL i x),hdL,hwL⟩
  let du:Fin 3→E→ℝ:=fun i x=>dH i x+dL i x
  have hdu:∀i,MemLp (du i) 2 (volume.restrict O):=fun i=>(Lp.memLp (dH i)).add (hdL i)
  have hweak:∀i,HasWeakPartialDeriv i (du i) (fullModelPhysicalField hκ0 hκ1 p f) O:=
    (wh.add wl).isWeakGrad
  have heSum:=nativeWeakEquation_add (fun i=>Lp.memLp (dH i)) hdL hgH hgL heH heL
  let g:=fun x=>halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8+
    nativeHalfEndPotentialCoefficient p.potential x*fullModelPhysicalField hκ0 hκ1 p f x
  have hsame:(fun x=>gH x+gL x) =ᵐ[volume.restrict O] g:=by
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    have hf:=nativePhysicalForcing_source_split G x
    have hf0:=halfEndSourceCylinder_physicalForcing (halfEndPhysicalH2SourceGraphValue f)
      (by simpa using hx.2) (le_of_lt (by simpa using hx.1))
    change fH x+fL x=physicalForcing (fun a:ℝ × S=>Real.exp (-2*a.1)*G a) x at hf
    rw [hf0] at hf
    change fH x/8+_ *uH x+(fL x/8+_ *uL x)=
      halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8+_ *(uH x+uL x)
    change fH x+fL x=halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x at hf
    linear_combination hf/8
  refine ⟨fullModelPhysicalField_H1 hκ0 hκ1 p f,(memLp_congr_ae hsame).mp (hgH.add hgL),du,hdu,hweak,?_⟩
  intro φ hφ hc hs
  exact (heSum φ hφ hc hs).trans (integral_congr_ae (hsame.mul (EventuallyEq.refl _ _)))

#print axioms nativeWeakEquation_add
#print axioms fullModelPhysicalField_same_weak_equation
end Yamabe3.Analysis.UniformElliptic
