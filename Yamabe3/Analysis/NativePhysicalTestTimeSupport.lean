import Yamabe3.Analysis.NativePhysicalPairTest

/-! A physical test supported in an actual polar time window gives a
full spectral L2 test supported in that SAME window. No angular modes
are discarded and the volume-dual weight remains unchanged. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay

 theorem nativePhysicalPairTestL2_time_support
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ)
    (A:Set ℝ) (hs:tsupport φ⊆nativePolarTimeWindow A):
    ∀ᵐt:ℝ∂volume,t∉A→nativePhysicalPairTestL2 φ hφ hc h0 t=0:=by
  filter_upwards [nativePhysicalPairTestL2_ae φ hφ hc h0] with t ht
  intro htA
  rw [ht]
  have hz(θ:SpherePolar.S):nativePhysicalPairTestPullback φ (t,θ)=0:=by
    have hnot:cylinderPoint (t,θ)∉tsupport φ:=by
      intro hp
      have hh: -Real.log ‖cylinderPoint (t,θ)‖∈A:=(hs hp).2
      exact htA (by simpa only [cylinderPoint_norm,Real.log_exp,neg_neg] using hh)
    simp only [nativePhysicalPairTestPullback,testPullback,image_eq_zero_of_notMem_tsupport hnot,mul_zero]
  have hzL:cylinderTestL2 (nativePhysicalPairTestPullback φ)
      (nativePhysicalPairTestPullback_smooth hφ).continuous t=0:=by
    apply Lp.ext
    have hh:=cylinderTestL2_ae (nativePhysicalPairTestPullback φ)
      (nativePhysicalPairTestPullback_smooth hφ).continuous t
    have hzero:((0:AngularL2):SpherePolar.S→ℝ)=ᵐ[angularVolume]0:=by
      simpa only [Measure.restrict_univ] using Lp.coeFn_zero ℝ 2 (angularVolume.restrict univ)
    apply ae_restrict_of_ae (s:=univ)
    filter_upwards [hh,hzero] with θ hθ hz0
    change _=(0:AngularL2) θ
    rw [hθ,hz θ,hz0]
    rfl
  change angularBasis.repr (cylinderTestL2 _ _ t)=0
  rw [hzL,map_zero]

#print axioms nativePhysicalPairTestL2_time_support
end Yamabe3.Analysis.SpherePolar
