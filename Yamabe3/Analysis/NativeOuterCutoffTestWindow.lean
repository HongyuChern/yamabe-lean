import Yamabe3.Analysis.NativeScaledCutoffGeometry
import Yamabe3.Analysis.NativePhysicalTestTimeSupport

/-! The SAME compactly cutoff exterior test lies in the complete finite
outer time window. This justifies whole-source reconstruction without
imposing a near-window support assumption on the original test. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay SphereSpectrum

 theorem nativeOuterCutoff_physical_test_window
    {χ φ:E→ℝ} (hsχ:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    (hsφ:tsupport φ⊆{x:E|1<‖x‖}) {N:ℕ} {S:ℝ} (hcover:-S+1/2<(N:ℝ)/2):
    tsupport (fun x:E=>χ (Real.exp S • x)*φ x)⊆nativePolarTimeWindow (Ioc (-(N:ℝ)/2) 0):=by
  intro x hx
  have hinner:1<‖x‖:=hsφ (tsupport_mul_subset_right hx)
  have houter:‖x‖<Real.exp ((1/8:ℝ)-S):=by
    have hh:=mem_ball_zero_iff.mp (nativeScaledCutoff_support hsχ S (tsupport_mul_subset_left hx))
    rw [←Real.exp_add] at hh
    simpa only [sub_eq_add_neg] using hh
  have hn:0<‖x‖:=by linarith
  have hl:=Real.log_lt_log hn houter
  rw [Real.log_exp] at hl
  refine ⟨norm_pos_iff.mp hn,?_,?_⟩
  · linarith
  · have hh:=Real.log_nonneg hinner.le
    linarith

 theorem nativeOuterCutoff_spectral_test_window
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hsχ:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ)
    (hsφ:tsupport φ⊆{x:E|1<‖x‖}) {N:ℕ} {S:ℝ} (hcover:-S+1/2<(N:ℝ)/2):
    let ψ:E→ℝ:=fun x=>χ (Real.exp S • x)*φ x
    let hψ:ContDiff ℝ ∞ ψ:=(hχ.comp (contDiff_id.const_smul _)).mul hφ
    let hcψ:HasCompactSupport ψ:=hc.mul_left
    let h0ψ:(0:E)∉tsupport ψ:=fun h=>h0 (tsupport_mul_subset_right h)
    ∀ᵐt:ℝ∂volume,t∉Ioc (-(N:ℝ)/2) 0→nativePhysicalPairTestL2 ψ hψ hcψ h0ψ t=0:=by
  dsimp only
  exact nativePhysicalPairTestL2_time_support _ _ _ _ _ (nativeOuterCutoff_physical_test_window hsχ hsφ hcover)

#print axioms nativeOuterCutoff_physical_test_window
#print axioms nativeOuterCutoff_spectral_test_window
end Yamabe3.Analysis.SpherePolar
