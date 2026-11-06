import Yamabe3.Analysis.NativePhysicalPairTestScaling

/-! The actual full L2 source paired against a constructed physical test
is exactly its Euclidean-volume pairing. Integrability follows from the
product L2 estimate, not from formal change-of-variable notation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem native_joint_memLp_of_memLp {U : ℝ → AngularL2} (hU : MemLp U 2)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ᵐt : ℝ ∂volume,(fun θ => w (t,θ))=ᵐ[angularVolume] (U t : S → ℝ)) :
    MemLp w 2 (volume.prod angularVolume) := by
  apply (memLp_two_iff_integrable_sq hw.aestronglyMeasurable).mpr
  apply (integrable_prod_iff (hw.pow_const 2).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hae] with t ht
    have hu : MemLp (U t : S → ℝ) 2 angularVolume := by
      simpa only [Measure.restrict_univ] using Lp.memLp (U t)
    exact (hu.ae_eq ht.symm).integrable_sq
  · have he : (fun t => ∫θ : S,‖w (t,θ)^2‖ ∂angularVolume)=ᵐ[volume] (fun t => ‖U t‖^2) := by
      filter_upwards [hae] with t ht
      simp only [Real.norm_of_nonneg (sq_nonneg _)]
      exact native_slice_square_eq ht
    exact ((memLp_two_iff_integrable_sq_norm hU.1).mp hU).congr he.symm

theorem nativePhysicalPairTest_log_pairing (w : ℝ × S → ℝ) (φ : E → ℝ) (p : ℝ × S) :
    logCylinderWeight (fun x => cylinderLift w x*φ x) p=
      w p*nativePhysicalPairTestPullback φ p := by
  change Real.exp (-3*p.1)*(cylinderLift w (Real.exp (-p.1) • (p.2:E))*φ (cylinderPoint p))=_
  rw [cylinderLift_smul _ (Real.exp_pos _) p.2,Real.log_exp,neg_neg,radialScale_exp_neg]
  have he : Real.exp (-3*p.1)*Real.exp (p.1/2)=Real.exp (-2*p.1)*Real.exp (-p.1/2) := by
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  change Real.exp (-3*p.1)*(Real.exp (p.1/2)*w p*φ (cylinderPoint p))=
    w p*(Real.exp (-2*p.1)*(Real.exp (-p.1/2)*φ (cylinderPoint p)))
  calc
    _=(Real.exp (-3*p.1)*Real.exp (p.1/2))*w p*φ (cylinderPoint p) := by ring
    _=_ := by rw [he];ring

variable (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
  (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (h0 : (0:E)∉tsupport φ)

def nativeFullPhysicalSourceRepresentative : E → ℝ :=
  cylinderLift (nativeAngularL2Joint (nativeL2FullAngularCLM F))

theorem nativeFullPhysicalSource_physical_test_pairing :
    Integrable (fun x => nativeFullPhysicalSourceRepresentative F x*φ x) ∧
      inner ℝ F (nativePhysicalPairTestL2 φ hφ hc h0)=
        ∫x : E,nativeFullPhysicalSourceRepresentative F x*φ x := by
  let w := nativeAngularL2Joint (nativeL2FullAngularCLM F)
  let q := nativePhysicalPairTestPullback φ
  have hw := nativeAngularL2Joint_measurable (nativeL2FullAngularCLM F)
  have hq := (nativePhysicalPairTestPullback_smooth hφ).continuous
  have hwm := native_joint_memLp_of_memLp (Lp.memLp (nativeL2FullAngularCLM F)) hw
    (Eventually.of_forall (nativeAngularL2Joint_ae (nativeL2FullAngularCLM F)))
  have hqm := native_joint_memLp_of_memLp
    ((contDiff_cylinderTestL2 (nativePhysicalPairTestPullback_smooth hφ)).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_cylinderTestL2 hq (nativePhysicalPairTestPullback_compact hc h0))) hq.measurable
    (Eventually.of_forall (fun t => (cylinderTestL2_ae q hq t).symm))
  have hm : Measurable (fun x => cylinderLift w x*φ x) := (measurable_cylinderLift hw).mul hφ.continuous.measurable
  have hlog : logCylinderWeight (fun x => cylinderLift w x*φ x)=(fun p => w p*q p) :=
    funext (nativePhysicalPairTest_log_pairing w φ)
  have hi : Integrable (logCylinderWeight (fun x => cylinderLift w x*φ x)) (volume.prod angularVolume) := by
    rw [hlog]
    exact hwm.integrable_mul hqm
  have hphys := (integrable_euclidean_iff_cylinder hm).mpr hi
  refine ⟨hphys,?_⟩
  change inner ℝ F (nativePhysicalPairTestL2 φ hφ hc h0)=∫x : E,cylinderLift w x*φ x
  rw [integral_euclidean_eq_cylinder hm hphys,L2.inner_def]
  change (∫t : ℝ,inner ℝ (F t) (nativePhysicalPairTestL2 φ hφ hc h0 t))=
    ∫t : ℝ,∫θ : S,logCylinderWeight (fun x => cylinderLift w x*φ x) (t,θ) ∂angularVolume
  rw [hlog]
  apply integral_congr_ae
  filter_upwards [nativeL2FullAngularCLM_ae F,nativePhysicalPairTestL2_ae φ hφ hc h0] with t hF hG
  have hqeq : cylinderTestL2 q hq t=angularBasis.repr.symm (nativePhysicalPairTestL2 φ hφ hc h0 t) := by
    rw [hG]
    exact (angularBasis.repr.symm_apply_apply _).symm
  have hangle : (∫θ : S,w (t,θ)*q (t,θ) ∂angularVolume)=
      inner ℝ (nativeL2FullAngularCLM F t) (cylinderTestL2 q hq t) := by
    rw [L2.inner_def,setIntegral_univ]
    apply integral_congr_ae
    filter_upwards [nativeAngularL2Joint_ae (nativeL2FullAngularCLM F) t,cylinderTestL2_ae q hq t] with θ hf hq
    change w (t,θ)*q (t,θ)=_
    simp only [RCLike.inner_apply,conj_trivial]
    change w (t,θ)*q (t,θ)=cylinderTestL2 q _ t θ*nativeL2FullAngularCLM F t θ
    change w (t,θ)=_ at hf
    rw [hq,hf]
    ring
  change inner ℝ (F t) (nativePhysicalPairTestL2 φ hφ hc h0 t)=∫θ : S,w (t,θ)*q (t,θ) ∂angularVolume
  rw [hangle,hF,hqeq]
  exact (angularBasis.repr.symm.inner_map_map _ _).symm

theorem nativeFullPhysicalSource_physical_test_pairing_on_ball
    (hs : tsupport φ⊆Metric.ball 0 1 \ {(0:E)}) :
    IntegrableOn (fun x => nativeFullPhysicalSourceRepresentative F x*φ x) (Metric.ball 0 1 \ {(0:E)}) ∧
      inner ℝ F (nativePhysicalPairTestL2 φ hφ hc h0)=
        ∫x in Metric.ball 0 1 \ {(0:E)},nativeFullPhysicalSourceRepresentative F x*φ x := by
  obtain ⟨hi,he⟩ := nativeFullPhysicalSource_physical_test_pairing F φ hφ hc h0
  refine ⟨hi.integrableOn,he.trans ?_⟩
  rw [←integral_indicator ((Metric.isOpen_ball.sdiff isClosed_singleton).measurableSet)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  by_cases hx : x∈Metric.ball 0 1 \ {(0:E)}
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx]
    change nativeFullPhysicalSourceRepresentative F x*φ x=0
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)),mul_zero]

#print axioms native_joint_memLp_of_memLp
#print axioms nativePhysicalPairTest_log_pairing
#print axioms nativeFullPhysicalSource_physical_test_pairing
#print axioms nativeFullPhysicalSource_physical_test_pairing_on_ball
end Yamabe3.Analysis.SpherePolar
