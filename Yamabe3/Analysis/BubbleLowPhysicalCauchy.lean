import Yamabe3.Analysis.BubbleLowAngularCauchy
import Yamabe3.Analysis.BubbleFinitePhysicalEquation
import Yamabe3.Analysis.NativeBubbleDelaunayCoupling
import Yamabe3.Analysis.Cylinder.NativeCylinderPullback
import Yamabe3.Analysis.Cylinder.NativeFiniteC2GradientEnergy

/-! Actual finite low exterior field, physical bubble equation and
both pointwise sphere Cauchy data. The radial one-half term and factor
8 are retained. This constructs the model low producer only; the native
geometric and high-mode matching is a separate obligation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum SpherePolar

def bubbleLowCylinderSource (H:ℝ →ᵇ AngularL2) (c:AngularIndex→ℝ) (p:ℝ × S):ℝ:=
  Real.exp (2*p.1)*nativeLowRepresentativeCLM (H (-p.1)) p.2+
    ∑i∈nativeLowIndexFinset,c i*bubbleCompensation i p.1*angularRepresentative i p.2

def bubbleLowPhysicalSource (H:ℝ →ᵇ AngularL2) (c:AngularIndex→ℝ) (x:E):ℝ:=
  8*cylinderLift (bubbleLowCylinderSource H c) x/‖x‖^2

theorem bubbleLow_source_identity (H:ℝ →ᵇ AngularL2) (c:AngularIndex→ℝ):
    finiteAngular nativeLowIndexFinset
      (fun i t=> -(Real.exp (2*t)*inner ℝ (angularBasis i) (H (-t))+c i*bubbleCompensation i t))=
      fun p=> -bubbleLowCylinderSource H c p:=by
  funext p
  simp only [finiteAngular,bubbleLowCylinderSource,nativeLowRepresentativeCLM_apply,
    Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem forcing_neg (v:ℝ × S→ℝ) (x:E):
    physicalForcing (fun p=> -v p) x=8*cylinderLift v x/‖x‖^2:=by
  by_cases hx:x=0
  · subst x
    simp only [physicalForcing,cylinderLift_zero,mul_zero,zero_div]
  · let y:puncturedSpace:=⟨x,hx⟩
    change physicalForcing (fun p=> -v p) (y:E)=8*cylinderLift v (y:E)/‖x‖^2
    rw [physicalForcing,cylinderLift_coe,cylinderLift_coe]
    dsimp only [puncturedCylinderLift,y]
    ring

theorem bubbleLow_finite_physical_equation (H:ℝ →ᵇ AngularL2) (c:AngularIndex→ℝ)
    (q:AngularIndex→ℝ→ℝ) (hq:∀i∈nativeLowIndexFinset,ContDiff ℝ 2 (q i))
    (heq:∀i∈nativeLowIndexFinset,∀t,
      deriv (deriv (q i)) t-bubbleLowCoefficient i t*q i t=
        -(Real.exp (2*t)*inner ℝ (angularBasis i) (H (-t))+c i*bubbleCompensation i t))
    {x:E} (hx:x≠0):
    -8*(∑j:Fin 3,fderiv ℝ (fun y=>fderiv ℝ (finitePhysical nativeLowIndexFinset q) y
        (EuclideanSpace.single j 1)) x (EuclideanSpace.single j 1))-
      30*(Real.sqrt (2/(1+‖x‖^2)))^4*finitePhysical nativeLowIndexFinset q x=
        bubbleLowPhysicalSource H c x:=by
  have hh:=native_finitePhysical_negative_trace_eq_global_C2
    (fun t=>(15/4)*fullBubbleDensity t) nativeLowIndexFinset q
    (fun i t=> -(Real.exp (2*t)*inner ℝ (angularBasis i) (H (-t))+c i*bubbleCompensation i t)) hq
    (fun i hi t=>by have he:=heq i hi t;unfold bubbleLowCoefficient at he;linarith) hx
  rw [bubbleLow_source_identity,forcing_neg] at hh
  have hc:((15/4)*fullBubbleDensity (-Real.log ‖x‖))/‖x‖^2=
      (15/4)*(Real.sqrt (2/(1+‖x‖^2)))^4:=by
    rw [fullBubbleDensity_physical _ (norm_pos_iff.mpr hx)]
    field_simp [norm_ne_zero_iff.mpr hx]
  rw [hc] at hh
  unfold bubbleLowPhysicalSource
  linear_combination 8*hh

private theorem finite_low_sphere_cauchy (q:AngularIndex→ℝ→ℝ)
    (hq:∀i∈nativeLowIndexFinset,ContDiff ℝ 2 (q i)) (t₀:ℝ) (d n:AngularL2)
    (hd:∀i∈nativeLowIndexFinset,q i t₀=inner ℝ (angularBasis i) d)
    (hn:∀i∈nativeLowIndexFinset,deriv (q i) t₀=inner ℝ (angularBasis i) n) (θ:S):
    finitePhysical nativeLowIndexFinset q (Real.exp (-t₀) • (θ:E))=
      Real.exp (t₀/2)*nativeLowRepresentativeCLM d θ ∧
    fderiv ℝ (finitePhysical nativeLowIndexFinset q) (Real.exp (-t₀) • (θ:E)) (θ:E)=
      -(Real.exp (t₀/2)/Real.exp (-t₀))*(nativeLowRepresentativeCLM n θ+nativeLowRepresentativeCLM d θ/2):=by
  have hr:=Real.exp_pos (-t₀)
  have hx:Real.exp (-t₀) • (θ:E)≠0:=by
    apply norm_ne_zero_iff.mp
    rw [norm_smul,Real.norm_of_nonneg hr.le,norm_eq_of_mem_sphere,mul_one]
    exact hr.ne'
  have ht: -Real.log (Real.exp (-t₀))=t₀:=by rw [Real.log_exp,neg_neg]
  have hval:finiteAngular nativeLowIndexFinset q (t₀,θ)=nativeLowRepresentativeCLM d θ:=by
    rw [nativeLowRepresentativeCLM_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hd i hi]
  have hnorm:finiteAngular nativeLowIndexFinset (fun i t=>deriv (q i) t+q i t/2) (t₀,θ)=
      nativeLowRepresentativeCLM n θ+nativeLowRepresentativeCLM d θ/2:=by
    simp only [nativeLowRepresentativeCLM_apply,finiteAngular,Finset.sum_div,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hd i hi,hn i hi]
    ring
  constructor
  · rw [finitePhysical_eq_lift,cylinderLift_smul _ hr,radialScale_exp_neg,ht,hval]
  · have hC:ContDiffAt ℝ 2 (finitePhysical nativeLowIndexFinset q)
        (Real.exp (-t₀) • (θ:E)):=
      (finitePhysical_contDiffOn_offZero_C2 _ _ hq).contDiffAt
        (isClosed_singleton.isOpen_compl.mem_nhds hx)
    rw [native_finitePhysical_radial_derivative _ _ hr θ
      (fun i hi=>(hq i hi).differentiable (by norm_num) _)
      (hC.differentiableAt (by norm_num)),radialScale_exp_neg,ht,hnorm]

/-- Model exterior low producer with the original source coordinates,
actual compensation coefficients, physical equation and both literal
Cauchy traces of one and the same field. -/
theorem exists_actual_bubble_low_physical_cauchy (H:ℝ →ᵇ AngularL2)
    {t₀:ℝ} (ht:0<t₀) (d n:AngularL2):
    ∃(c:AngularIndex→ℝ) (q:AngularIndex→ℝ→ℝ),
      (∀i∈nativeLowIndexFinset,c i=bubbleLowCauchyCompensation i t₀
        (inner ℝ (angularBasis i) d) (inner ℝ (angularBasis i) n)
        (bubbleLowSourceMoment i (bubbleSourceCoordinate H i) t₀)) ∧
      ContDiffOn ℝ 2 (finitePhysical nativeLowIndexFinset q) ({0}ᶜ:Set E) ∧
      (∀x:E,x≠0→
        -8*(∑j:Fin 3,fderiv ℝ (fun y=>fderiv ℝ (finitePhysical nativeLowIndexFinset q) y
          (EuclideanSpace.single j 1)) x (EuclideanSpace.single j 1))-
          30*(Real.sqrt (2/(1+‖x‖^2)))^4*finitePhysical nativeLowIndexFinset q x=
            bubbleLowPhysicalSource H c x) ∧
      (∀θ:S,finitePhysical nativeLowIndexFinset q (Real.exp (-t₀) • (θ:E))=
        Real.exp (t₀/2)*nativeLowRepresentativeCLM d θ ∧
        fderiv ℝ (finitePhysical nativeLowIndexFinset q) (Real.exp (-t₀) • (θ:E)) (θ:E)=
          -(Real.exp (t₀/2)/Real.exp (-t₀))*(nativeLowRepresentativeCLM n θ+nativeLowRepresentativeCLM d θ/2)) ∧
      (∀i∈nativeLowIndexFinset,Tendsto (q i) atBot (𝓝 0) ∧ Tendsto (deriv (q i)) atBot (𝓝 0)):=by
  obtain ⟨c,q,hq,_,_⟩:=exists_actual_angular_low_cauchy_solver H ht d n
  refine ⟨c,q,(fun i hi=>(hq i hi).1),finitePhysical_contDiffOn_offZero_C2 _ _
    (fun i hi=>(hq i hi).2.1),?_,?_,?_⟩
  · intro x hx
    exact bubbleLow_finite_physical_equation H c q (fun i hi=>(hq i hi).2.1)
      (fun i hi=>(hq i hi).2.2.1) hx
  · exact finite_low_sphere_cauchy q (fun i hi=>(hq i hi).2.1) t₀ d n
      (fun i hi=>(hq i hi).2.2.2.1) (fun i hi=>(hq i hi).2.2.2.2.1)
  · exact fun i hi=>(hq i hi).2.2.2.2.2

#print axioms bubbleLow_source_identity
#print axioms bubbleLow_finite_physical_equation
#print axioms exists_actual_bubble_low_physical_cauchy
end Yamabe3.Analysis.Delaunay
