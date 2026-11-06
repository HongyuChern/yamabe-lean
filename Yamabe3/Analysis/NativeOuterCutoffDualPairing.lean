import Yamabe3.Analysis.NativeOuterCutoffActualOperator
import Yamabe3.Analysis.NativePhysicalPairTestScaling

/-! Exact operator/test duality for the actual outer cutoff. Moving a
cutoff to the SAME smooth physical test preserves every full angular
mode, then exposes precisely the commutator and cutoff-product geometry. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay SphereSpectrum

 theorem nativeOuterCutoff_source_dual_pairing
    (S s:ℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (U:NativeCollarL2)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ):
    let ψ:E→ℝ:=fun x=>χ (Real.exp S • x)*φ x
    let hψ:ContDiff ℝ ∞ ψ:=(hχ.comp (contDiff_id.const_smul _)).mul hφ
    let hcψ:HasCompactSupport ψ:=hc.mul_left
    let h0ψ:(0:E)∉tsupport ψ:=fun h=>h0 (tsupport_mul_subset_right h)
    inner ℝ (nativeFullShellSourceReturnCLM s
      (nativeCollarScalarMulCLM (nativeOuterFieldCutoffAtScale S s χ)
        (nativeOuterFieldCutoffAtScale_smooth S s hχ).continuous U)) (nativePhysicalPairTestL2 φ hφ hc h0)=
      inner ℝ (nativeFullShellSourceReturnCLM s U) (nativePhysicalPairTestL2 ψ hψ hcψ h0ψ):=by
  dsimp only
  rw [nativeFullShellSourceReturn_physical_test,nativeFullShellSourceReturn_physical_test]
  congr 1
  apply integral_congr_ae
  have hμ:volume.restrict nativeSourceShell≤volume.restrict nativePoissonEntranceCollar:=
    Measure.restrict_mono nativeSourceShell_subset_collar le_rfl
  filter_upwards [ae_mono hμ (nativeCollarScalarMulCLM_ae (nativeOuterFieldCutoffAtScale S s χ)
    (nativeOuterFieldCutoffAtScale_smooth S s hχ).continuous U)] with x hx
  rw [hx]
  have hs:Real.exp (S-s) • x=Real.exp S • (Real.exp (-s) • x):=by
    rw [smul_smul,←Real.exp_add]
    congr 1
  simp only [nativeOuterFieldCutoffAtScale,hs]
  ring

 theorem nativeOuterCutoff_full_operator_dual_pairing
    (g:RiemannianMetric 3 E) (a S s:ℝ) (V:ℝ→ᵇℝ)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (J:nativeCollarJetClosure)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ):
    let χs:=nativeOuterFieldCutoffAtScale S s χ
    let hχs:=nativeOuterFieldCutoffAtScale_smooth S s hχ
    let ψ:E→ℝ:=fun x=>χ (Real.exp S • x)*φ x
    let hψ:ContDiff ℝ ∞ ψ:=(hχ.comp (contDiff_id.const_smul _)).mul hφ
    let hcψ:HasCompactSupport ψ:=hc.mul_left
    let h0ψ:(0:E)∉tsupport ψ:=fun h=>h0 (tsupport_mul_subset_right h)
    inner ℝ (nativeFullShellSourceReturnCLM s
      ((nativeFlatCollarJetCLM V+nativeBCFCollarErrorCLM g a V) (nativeCollarCutoffCLM χs hχs J).val))
      (nativePhysicalPairTestL2 φ hφ hc h0)=
      inner ℝ (nativeFullShellSourceReturnCLM s (nativeFlatCollarJetCLM V J.val)) (nativePhysicalPairTestL2 ψ hψ hcψ h0ψ)+
      inner ℝ (nativeFullShellSourceReturnCLM s (nativeCollarCutoffCommutatorCLM χs hχs J.val)) (nativePhysicalPairTestL2 φ hφ hc h0)+
      inner ℝ (nativeFullShellSourceReturnCLM s (nativeBCFCollarErrorCLM g a V (nativeCollarCutoffCLM χs hχs J).val))
        (nativePhysicalPairTestL2 φ hφ hc h0):=by
  dsimp only
  rw [ContinuousLinearMap.add_apply,nativeFlatCollar_cutoff_exact_source]
  simp only [map_add,inner_add_left]
  rw [nativeOuterCutoff_source_dual_pairing S s χ hχ]

#print axioms nativeOuterCutoff_source_dual_pairing
#print axioms nativeOuterCutoff_full_operator_dual_pairing
end Yamabe3.Analysis.SpherePolar
