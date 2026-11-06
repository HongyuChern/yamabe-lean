import Yamabe3.Analysis.NativeLowReverseL2ValueTrace
import Yamabe3.Analysis.NativeL2HalfNormalTrace

/-! The genuine radial trace of the low solution is the same canonical
entrance derivative with the physical conformal factor -5/2. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0≤v t ∧ v t≤1)

def nativeLowReverseL2NormalAngularCLM : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] AngularL2 :=
  (nativeLowProjection.comp angularBasis.repr.symm.toLinearIsometry.toContinuousLinearMap).comp
    ((-5/2:ℝ) • lowL2EntranceCLM (lowAngularOperatorBCF v hv hb) (lowAngularOperatorBCF_norm_le v hv hb)+
      lowL2EntranceDerivativeCLM (lowAngularOperatorBCF v hv hb) (lowAngularOperatorBCF_norm_le v hv hb))

theorem nativeLowReverseL2_finite_normal (F : ℝ →ᵇ AngularSpectralSpace) (hF : MemLp F 2) (θ : S) :
    fderiv ℝ (nativeLowReverseL2PhysicalField v hv hb (hF.toLp F)) (θ:E) (θ:E)=
      finiteAngular nativeLowIndexFinset (fun i _ =>
        (-5/2)*lowL2ContinuousCLM (lowAngularOperatorBCF v hv hb) (lowAngularOperatorBCF_norm_le v hv hb) (hF.toLp F) 0 i+
          lowL2DerivativeCLM (lowAngularOperatorBCF v hv hb) (lowAngularOperatorBCF_norm_le v hv hb) (hF.toLp F) 0 i) (0,θ) := by
  let A := lowAngularOperatorBCF v hv hb
  let hA := lowAngularOperatorBCF_norm_le v hv hb
  let U := lowL2ContinuousCLM A hA (hF.toLp F)
  let D := lowL2DerivativeCLM A hA (hF.toLp F)
  let q := fun i t => Real.exp (2*t)*U (-t) i
  have hq (i : AngularIndex) (hi : i∈nativeLowIndexFinset) :=
    (nativeLowL2_reversed_coefficient_C2 v hv hb F hF i ((mem_nativeLowIndexFinset i).mp hi)).1
  have hx : (θ:E)≠0 := by
    intro he
    have hn := norm_eq_of_mem_sphere θ
    rw [he,norm_zero] at hn
    norm_num at hn
  have hu := (finitePhysical_contDiffOn_offZero_C2 nativeLowIndexFinset q (fun i hi => hq i hi)).contDiffAt
    (isClosed_singleton.isOpen_compl.mem_nhds hx)
  have hr := native_finitePhysical_radial_derivative nativeLowIndexFinset q (by norm_num : (0:ℝ)<1) θ
    (fun i hi => (hq i hi).differentiable (by norm_num) _)
    (by simpa only [one_smul] using hu.differentiableAt (by norm_num))
  have hscale : radialScale 1=1 := by simp [radialScale]
  simp only [one_smul,Real.log_one,neg_zero,hscale,div_one,neg_one_mul] at hr
  change fderiv ℝ (finitePhysical nativeLowIndexFinset q) (θ:E) (θ:E)=_
  rw [hr]
  change -finiteAngular nativeLowIndexFinset (fun i t => deriv (q i) t+q i t/2) (0,θ)=_
  unfold finiteAngular
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hdU := (lp.evalCLM ℝ (fun _ : AngularIndex => ℝ) 2 i).hasFDerivAt.comp_hasDerivAt 0
    (lowL2Continuous_hasDerivAt A hA (hF.toLp F) 0)
  change HasDerivAt (fun t => U t i) (D 0 i) 0 at hdU
  have hdUr : HasDerivAt (fun t => U (-t) i) (-D 0 i) 0 := by
    have hdU' : HasDerivAt (fun t => U t i) (D 0 i) ((-id : ℝ→ℝ) 0) := by simpa using hdU
    simpa only [Function.comp_def,Pi.neg_apply,id_eq,mul_neg,mul_one] using hdU'.comp 0 ((hasDerivAt_id (0:ℝ)).neg)
  have hdq := ((Real.hasDerivAt_exp ((2:ℝ)*0)).comp 0 ((hasDerivAt_id (0:ℝ)).const_mul 2)).mul hdUr
  have hd : deriv (q i) 0=2*U 0 i-D 0 i := by
    change HasDerivAt (q i) (Real.exp (2*0)*(2*1)*U (-0) i+Real.exp (2*0)*(-D 0 i)) 0 at hdq
    simpa only [mul_zero,Real.exp_zero,one_mul,mul_one,neg_zero,sub_eq_add_neg] using hdq.deriv
  change -((deriv (q i) 0+q i 0/2)*angularRepresentative i θ)=((-5/2)*U 0 i+D 0 i)*angularRepresentative i θ
  rw [hd]
  dsimp only [q]
  simp only [mul_zero,Real.exp_zero,one_mul,neg_zero]
  ring

theorem nativeLowReverseL2Jet_normal_trace (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeCollarNormalTraceCLM (nativeLowReverseL2JetCLM v hv hb F)=
      nativeAngularTraceCLM (nativeLowReverseL2NormalAngularCLM v hv hb F) := by
  have hc := isClosed_eq
    (nativeCollarNormalTraceCLM.continuous.comp (nativeLowReverseL2JetCLM v hv hb).continuous)
    (nativeAngularTraceCLM.continuous.comp (nativeLowReverseL2NormalAngularCLM v hv hb).continuous)
  refine (continuousL2SourceInclusion_dense AngularSpectralSpace).induction_on F hc ?_
  intro H
  rw [nativeLowReverseL2Jet_agrees_C2,(nativeCollarTraceCLM_agrees_C2 _).2]
  let A := lowAngularOperatorBCF v hv hb
  let hA := lowAngularOperatorBCF_norm_le v hv hb
  let U := lowL2ContinuousCLM A hA (continuousL2SourceInclusion _ H)
  let D := lowL2DerivativeCLM A hA (continuousL2SourceInclusion _ H)
  let b : AngularSpectralSpace := (-5/2:ℝ) • U 0+D 0
  have he : (∑ i ∈ nativeLowIndexFinset,((-5/2)*U 0 i+D 0 i) • angularBasis i)=
      nativeLowReverseL2NormalAngularCLM v hv hb (continuousL2SourceInclusion _ H) := by
    change _=nativeLowProjection (angularBasis.repr.symm b)
    rw [nativeLowProjection_eq_finite,finiteHilbertProjection]
    apply Finset.sum_congr rfl
    intro i hi
    rw [←HilbertBasis.repr_apply_apply,LinearIsometryEquiv.apply_symm_apply]
    rfl
  have ha := finiteAngular_ae nativeLowIndexFinset (fun i (_ : ℝ) => (-5/2)*U 0 i+D 0 i) 0
  rw [he] at ha
  apply Lp.ext
  filter_upwards [nativeC2NormalTraceLinear_ae (nativeLowReverseL2ContinuousFieldLinear v hv hb H),ha,
    nativeAngularTraceCLM_ae (nativeLowReverseL2NormalAngularCLM v hv hb (continuousL2SourceInclusion _ H))] with θ ht ha hm
  rw [ht,hm]
  change fderiv ℝ (nativeLowReverseL2PhysicalField v hv hb (continuousL2SourceInclusion _ H)) (θ:E) (θ:E)=_
  exact (nativeLowReverseL2_finite_normal v hv hb H.val H.property θ).trans ha

#print axioms nativeLowReverseL2_finite_normal
#print axioms nativeLowReverseL2Jet_normal_trace
end Yamabe3.Analysis.SpherePolar
