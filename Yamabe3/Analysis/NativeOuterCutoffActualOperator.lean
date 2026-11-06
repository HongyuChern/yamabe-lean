import Yamabe3.Analysis.NativeFlatCutoffRowIdentity
import Yamabe3.Analysis.NativeBCFWeakPhysicalRow
import Yamabe3.Analysis.NativeOuterCutoffGeometricSender

/-! The actual far residual is EXACTLY the cutoff commutator plus the
geometry of the cutoff product of ONE field. No geometry product terms
are omitted and no independent outer representative is substituted. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay

 theorem nativeFullBCF_cutoff_exact_residual
    (g:RiemannianMetric 3 E) (r:ℝ) (V:ℝ→ᵇℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (J:nativeCollarJetClosure):
    (nativeFlatCollarJetCLM V+nativeBCFCollarErrorCLM g r V) (nativeCollarCutoffCLM χ hχ J).val-
      nativeCollarScalarMulCLM χ hχ.continuous (nativeFlatCollarJetCLM V J.val)=
    nativeCollarCutoffCommutatorCLM χ hχ J.val+
      nativeBCFCollarErrorCLM g r V (nativeCollarCutoffCLM χ hχ J).val:=by
  rw [ContinuousLinearMap.add_apply,nativeFlatCollar_cutoff_exact_source]
  abel

 theorem nativeOuterCutoff_same_physical_field
    (S s:ℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (J:nativeCollarJetClosure) {u:E→ℝ}
    (hJ:(J.val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x=>Real.exp (3*s/2)*u (Real.exp (-s) • x))):
    ((nativeCollarCutoffCLM (nativeOuterFieldCutoffAtScale S s χ)
      (nativeOuterFieldCutoffAtScale_smooth S s hχ) J).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x=>Real.exp (3*s/2)*(χ (Real.exp S • (Real.exp (-s) • x))*u (Real.exp (-s) • x))):=by
  apply (nativeCollarCutoffCLM_value_ae (nativeOuterFieldCutoffAtScale S s χ)
    (nativeOuterFieldCutoffAtScale_smooth S s hχ) J).trans
  filter_upwards [hJ] with x hx
  change nativeOuterFieldCutoffAtScale S s χ x*J.val.1 x=_
  rw [hx]
  have hs:Real.exp (S-s) • x=Real.exp S • (Real.exp (-s) • x):=by
    rw [smul_smul,←Real.exp_add]
    congr 1
  simp only [nativeOuterFieldCutoffAtScale,hs]
  ring

#print axioms nativeFullBCF_cutoff_exact_residual
#print axioms nativeOuterCutoff_same_physical_field
end Yamabe3.Analysis.SpherePolar
