import Yamabe3.Analysis.NativePoissonExteriorCollarTrace
import Yamabe3.Analysis.NativeCollarJetWeakDerivatives

/-! A finite actual C2 physical field, its genuine H2 collar jet, and
both literal sphere traces. This will carry the constructed low modes. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeFiniteCollarJet (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ)
    (hq : ∀ i∈s,ContDiff ℝ 2 (q i)) : nativeCollarJetClosure :=
  nativeC2CollarJetInclusion ⟨finitePhysical s q,finitePhysical_contDiffOn_offZero_C2 s q hq⟩

theorem nativeFiniteCollar_entrance (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ)
    (hq : ∀ i∈s,ContDiff ℝ 2 (q i)) (θ : S) :
    finitePhysical s q (θ:E)=finiteAngular s q (0,θ) ∧
    fderiv ℝ (finitePhysical s q) (θ:E) (θ:E)=
      -finiteAngular s (fun i t => deriv (q i) t+q i t/2) (0,θ) := by
  have hx : (θ:E)≠0 := by
    intro he
    have h := norm_eq_of_mem_sphere θ
    rw [he,norm_zero] at h
    norm_num at h
  have hu := (finitePhysical_contDiffOn_offZero_C2 s q hq).contDiffAt
    (isClosed_singleton.isOpen_compl.mem_nhds hx)
  have hr := native_finitePhysical_radial_derivative s q (by norm_num : (0:ℝ)<1) θ
    (fun i hi => (hq i hi).differentiable (by norm_num) _)
    (by simpa only [one_smul] using hu.differentiableAt (by norm_num))
  have hscale : radialScale 1=1 := by simp [radialScale]
  simp only [one_smul,Real.log_one,neg_zero,hscale,div_one,neg_one_mul] at hr
  refine ⟨?_,hr⟩
  rw [finitePhysical_eq_lift,native_cylinderLift_sphere]

theorem nativeFiniteCollarJet_value_trace (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ)
    (hq : ∀ i∈s,ContDiff ℝ 2 (q i)) :
    nativeCollarValueTraceCLM (nativeFiniteCollarJet s q hq)=
      nativeAngularTraceCLM (∑i∈s,q i 0 • angularBasis i) := by
  rw [nativeFiniteCollarJet,(nativeCollarTraceCLM_agrees_C2 _).1]
  apply Lp.ext
  filter_upwards [nativeC2ValueTraceLinear_ae
    ⟨finitePhysical s q,finitePhysical_contDiffOn_offZero_C2 s q hq⟩,
    finiteAngular_ae s q 0,nativeAngularTraceCLM_ae (∑i∈s,q i 0 • angularBasis i)] with θ ht ha hm
  rw [ht,hm]
  exact (nativeFiniteCollar_entrance s q hq θ).1.trans ha

theorem nativeFiniteCollarJet_normal_trace (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ)
    (hq : ∀ i∈s,ContDiff ℝ 2 (q i)) :
    nativeCollarNormalTraceCLM (nativeFiniteCollarJet s q hq)=
      nativeAngularTraceCLM (-(∑i∈s,(deriv (q i) 0+q i 0/2) • angularBasis i)) := by
  rw [nativeFiniteCollarJet,(nativeCollarTraceCLM_agrees_C2 _).2]
  let N : AngularL2 := ∑i∈s,(deriv (q i) 0+q i 0/2) • angularBasis i
  have hneg : (⇑(-N)) =ᵐ[angularVolume] (fun θ => -N θ) := by
    have h0 : (⇑(-N)) =ᵐ[angularVolume.restrict univ] (fun θ => -N θ) := Lp.coeFn_neg N
    filter_upwards [(ae_restrict_iff' MeasurableSet.univ).mp h0] with θ h
    exact h (mem_univ θ)
  apply Lp.ext
  filter_upwards [nativeC2NormalTraceLinear_ae
    ⟨finitePhysical s q,finitePhysical_contDiffOn_offZero_C2 s q hq⟩,
    finiteAngular_ae s (fun i t => deriv (q i) t+q i t/2) 0,
    nativeAngularTraceCLM_ae (-N),hneg] with θ ht ha hm hn
  rw [ht,hm,hn]
  exact (nativeFiniteCollar_entrance s q hq θ).2.trans (congrArg Neg.neg ha)

#print axioms nativeFiniteCollar_entrance
#print axioms nativeFiniteCollarJet_value_trace
#print axioms nativeFiniteCollarJet_normal_trace
end Yamabe3.Analysis.SpherePolar
