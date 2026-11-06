import Yamabe3.Analysis.NativePhysicalSourceDuality

/-! The actual far cutoff preserves the ORIGINAL supported source
pairing. Its plateau is proved on every relevant cylinder slice; the
source support is used only almost everywhere in time. No source is
silently replaced by its truncated value. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay

theorem nativeFarCutoff_one_on_supported_slice
    {χ:E→ℝ} (h1:∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χ=ᶠ[𝓝 x](fun _=>1))
    {b S:ℝ} (hS:S ≤ b-1) {t:ℝ} (ht:b ≤ t) (θ:SpherePolar.S) :
    χ (Real.exp S • cylinderPoint (t,θ))=1 := by
  have hh:‖Real.exp S • cylinderPoint (t,θ)‖ ≤ Real.exp (-(1/8:ℝ)) := by
    rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,cylinderPoint_norm,←Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  exact (h1 _ (by simpa only [mem_closedBall,dist_zero_right] using hh)).self_of_nhds

theorem nativeSupportedSource_cutoff_test_pairing
    {χ:E→ℝ} (hχ:ContDiff ℝ ∞ χ)
    (h1:∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χ=ᶠ[𝓝 x](fun _=>1))
    {b S:ℝ} (hS:S ≤ b-1)
    (F:Lp AngularSpectralSpace 2 (volume:Measure ℝ))
    (hF:∀ᵐt:ℝ∂volume,t < b → F t=0)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ) :
    let ψ:E→ℝ:=fun x=>χ (Real.exp S • x)*φ x
    let hψ:ContDiff ℝ ∞ ψ:=(hχ.comp (contDiff_id.const_smul _)).mul hφ
    let hcψ:HasCompactSupport ψ:=hc.mul_left
    let h0ψ:(0:E)∉tsupport ψ:=fun h=>h0 (tsupport_mul_subset_right h)
    inner ℝ F (nativePhysicalPairTestL2 ψ hψ hcψ h0ψ)=inner ℝ F (nativePhysicalPairTestL2 φ hφ hc h0) := by
  dsimp only
  let ψ:E→ℝ:=fun x=>χ (Real.exp S • x)*φ x
  have hψ:ContDiff ℝ ∞ ψ:=(hχ.comp (contDiff_id.const_smul _)).mul hφ
  have hcψ:HasCompactSupport ψ:=hc.mul_left
  have h0ψ:(0:E)∉tsupport ψ:=fun h=>h0 (tsupport_mul_subset_right h)
  have hcurve (t:ℝ) (ht:b ≤ t):nativePhysicalPairTestCurve ψ hψ t=nativePhysicalPairTestCurve φ hφ t := by
    apply congrArg angularBasis.repr
    apply Lp.ext
    filter_upwards [ae_restrict_of_ae (s:=univ) (cylinderTestL2_ae (nativePhysicalPairTestPullback ψ) (nativePhysicalPairTestPullback_smooth hψ).continuous t),
      ae_restrict_of_ae (s:=univ) (cylinderTestL2_ae (nativePhysicalPairTestPullback φ) (nativePhysicalPairTestPullback_smooth hφ).continuous t)] with θ hψθ hφθ
    rw [hψθ,hφθ]
    change Real.exp (-2*t)*(Real.exp (-t/2)*(χ (Real.exp S • cylinderPoint (t,θ))*φ (cylinderPoint (t,θ))))=
      Real.exp (-2*t)*(Real.exp (-t/2)*φ (cylinderPoint (t,θ)))
    rw [nativeFarCutoff_one_on_supported_slice h1 hS ht θ,one_mul]
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hF,nativePhysicalPairTestL2_ae ψ hψ hcψ h0ψ,nativePhysicalPairTestL2_ae φ hφ hc h0] with t hf hψt hφt
  by_cases ht:t < b
  · rw [hf ht]
    simp
  · rw [hψt,hφt,hcurve t (le_of_not_gt ht)]

theorem nativeSupportedSource_cutoff_physical_pairing
    {χ:E→ℝ} (hχ:ContDiff ℝ ∞ χ)
    (h1:∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χ=ᶠ[𝓝 x](fun _=>1))
    {b S:ℝ} (hS:S ≤ b-1)
    (F:Lp AngularSpectralSpace 2 (volume:Measure ℝ))
    (hF:∀ᵐt:ℝ∂volume,t < b → F t=0)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ) :
    (∫x:E,nativeFullPhysicalSourceRepresentative F x*(χ (Real.exp S • x)*φ x))=
      ∫x:E,nativeFullPhysicalSourceRepresentative F x*φ x := by
  let ψ:E→ℝ:=fun x=>χ (Real.exp S • x)*φ x
  have hψ:ContDiff ℝ ∞ ψ:=(hχ.comp (contDiff_id.const_smul _)).mul hφ
  have hcψ:HasCompactSupport ψ:=hc.mul_left
  have h0ψ:(0:E)∉tsupport ψ:=fun h=>h0 (tsupport_mul_subset_right h)
  rw [←(nativeFullPhysicalSource_physical_test_pairing F ψ hψ hcψ h0ψ).2,
    ←(nativeFullPhysicalSource_physical_test_pairing F φ hφ hc h0).2]
  exact nativeSupportedSource_cutoff_test_pairing hχ h1 hS F hF φ hφ hc h0

#print axioms nativeFarCutoff_one_on_supported_slice
#print axioms nativeSupportedSource_cutoff_test_pairing
#print axioms nativeSupportedSource_cutoff_physical_pairing
end Yamabe3.Analysis.SpherePolar
