import Yamabe3.Analysis.NativeFullSourceReconstruction
import Yamabe3.Analysis.NativeCylinderTestCurve

/-! Compact physical tests produce actual full spectral L2 tests. The
extra exp(-2t) is the volume-dual weight, not a change of the PDE source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativePhysicalPairTestPullback (φ : E → ℝ) (p : ℝ × S) : ℝ :=
  Real.exp (-2*p.1)*testPullback φ p

theorem nativePhysicalPairTestPullback_smooth {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContMDiff (𝓘(ℝ,ℝ).prod (𝓡 2)) 𝓘(ℝ,ℝ) ∞ (nativePhysicalPairTestPullback φ) :=
  (Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul contMDiff_fst)).mul (smooth_testPullback hφ)

theorem nativePhysicalPairTestPullback_compact {φ : E → ℝ}
    (hc : HasCompactSupport φ) (h0 : (0:E)∉tsupport φ) :
    HasCompactSupport (nativePhysicalPairTestPullback φ) :=
  (hasCompactSupport_testPullback hc h0).mul_left

variable (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (h0 : (0:E)∉tsupport φ)

def nativePhysicalPairTestCurve (t : ℝ) : AngularSpectralSpace :=
  angularBasis.repr (cylinderTestL2 (nativePhysicalPairTestPullback φ)
    (nativePhysicalPairTestPullback_smooth hφ).continuous t)

theorem nativePhysicalPairTestCurve_continuous : Continuous (nativePhysicalPairTestCurve φ hφ) :=
  angularBasis.repr.continuous.comp (contDiff_cylinderTestL2 (nativePhysicalPairTestPullback_smooth hφ)).continuous

include hc h0 in
theorem nativePhysicalPairTestCurve_compact : HasCompactSupport (nativePhysicalPairTestCurve φ hφ) := by
  apply (hasCompactSupport_cylinderTestL2 (nativePhysicalPairTestPullback_smooth hφ).continuous
    (nativePhysicalPairTestPullback_compact hc h0)).comp_left
  exact angularBasis.repr.map_zero

def nativePhysicalPairTestL2 : Lp AngularSpectralSpace 2 (volume : Measure ℝ) :=
  ((nativePhysicalPairTestCurve_continuous φ hφ).memLp_of_hasCompactSupport
    (nativePhysicalPairTestCurve_compact φ hφ hc h0)).toLp (nativePhysicalPairTestCurve φ hφ)

theorem nativePhysicalPairTestL2_ae :
    (nativePhysicalPairTestL2 φ hφ hc h0 : ℝ → AngularSpectralSpace)=ᵐ[volume] nativePhysicalPairTestCurve φ hφ :=
  ((nativePhysicalPairTestCurve_continuous φ hφ).memLp_of_hasCompactSupport
    (nativePhysicalPairTestCurve_compact φ hφ hc h0)).coeFn_toLp

theorem nativePhysicalPairTestL2_positive
    (hs : tsupport φ⊆Metric.ball 0 1 \ {(0:E)}) :
    ∀ᵐt : ℝ ∂volume,t≤0 → nativePhysicalPairTestL2 φ hφ hc h0 t=0 := by
  filter_upwards [nativePhysicalPairTestL2_ae φ hφ hc h0] with t ht
  intro ht0
  rw [ht]
  have hz (θ : S) : nativePhysicalPairTestPullback φ (t,θ)=0 := by
    have hnot : cylinderPoint (t,θ)∉tsupport φ := fun hx =>
      (not_lt_of_ge ht0) ((cylinderPoint_mem_punctured_unit_ball_iff (t,θ)).mp (hs hx))
    simp only [nativePhysicalPairTestPullback,testPullback,image_eq_zero_of_notMem_tsupport hnot,mul_zero]
  have hzL : cylinderTestL2 (nativePhysicalPairTestPullback φ)
      (nativePhysicalPairTestPullback_smooth hφ).continuous t=0 := by
    apply Lp.ext
    have h := cylinderTestL2_ae (nativePhysicalPairTestPullback φ)
      (nativePhysicalPairTestPullback_smooth hφ).continuous t
    have hz' : ((0:AngularL2) : S → ℝ)=ᵐ[angularVolume] 0 := by
      simpa only [Measure.restrict_univ] using (Lp.coeFn_zero ℝ 2 (angularVolume.restrict univ))
    apply ae_restrict_of_ae (s := univ)
    filter_upwards [h,hz'] with θ hθ hzero
    change _=(0:AngularL2) θ
    rw [hθ,hz θ,hzero]
    rfl
  change angularBasis.repr (cylinderTestL2 _ _ t)=0
  rw [hzL,map_zero]

theorem nativePhysicalPairTestL2_shift_lift (s : ℝ) :
    (nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s
      (nativePhysicalPairTestL2 φ hφ hc h0)) : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      cylinderLift (fun p => nativePhysicalPairTestPullback φ (p.1+s,p.2)) := by
  apply nativeL2FullPhysicalSource_eq_lift _
    (((nativePhysicalPairTestPullback_smooth hφ).continuous.measurable).comp
      ((measurable_fst.add_const s).prodMk measurable_snd))
  have ht := (measurePreserving_add_right (volume : Measure ℝ) s).quasiMeasurePreserving.ae
    (nativePhysicalPairTestL2_ae φ hφ hc h0)
  filter_upwards [l2TimeTranslate_ae AngularSpectralSpace s (nativePhysicalPairTestL2 φ hφ hc h0),ht] with t htr hcurve
  rw [htr,hcurve]
  change (fun θ => nativePhysicalPairTestPullback φ (t+s,θ))=ᵐ[angularVolume]
    (angularBasis.repr.symm (angularBasis.repr (cylinderTestL2 _ _ (t+s))) : S → ℝ)
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact (cylinderTestL2_ae _ _ (t+s)).symm

#print axioms nativePhysicalPairTestPullback_smooth
#print axioms nativePhysicalPairTestCurve_compact
#print axioms nativePhysicalPairTestL2_positive
#print axioms nativePhysicalPairTestL2_shift_lift
end Yamabe3.Analysis.SpherePolar
