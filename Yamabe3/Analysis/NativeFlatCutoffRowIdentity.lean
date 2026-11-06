import Yamabe3.Analysis.NativeCollarJetMultiplier
import Yamabe3.Analysis.NativeCollarCutoffCommutator
import Yamabe3.Analysis.NativeOrbitWeakJacobian
import Yamabe3.Analysis.WeakCutoffCommutatorIdentity
import Yamabe3.Analysis.NativeTrueEntranceH4Solver

/-! Exact flat operator product identity on EVERY closed collar jet.
The cutoff commutator is the actual first/second derivative residual of
the same field; the potential part cancels without being discarded. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay

 theorem nativeFlatCollar_cutoff_exact_source (V:ℝ→ᵇℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (J:nativeCollarJetClosure):
    nativeFlatCollarJetCLM V (nativeCollarCutoffCLM χ hχ J).val=
      nativeCollarScalarMulCLM χ hχ.continuous (nativeFlatCollarJetCLM V J.val)+
        nativeCollarCutoffCommutatorCLM χ hχ J.val:=by
  let K:=nativeCollarCutoffCLM χ hχ J
  have hv:=nativeCollarCutoffCLM_value_ae χ hχ J
  have hl:=weakNegativeLaplacian_congr_ae (nativePolarTimeWindow_open (1/2)) hv
  have hp:=weakNegativeLaplacian_cutoff_commutator (nativePolarTimeWindow_open (1/2))
    (nativePolarTimeWindow_precompact (1/2)) χ hχ (nativeCollarJetClosure_memH2 J)
  apply Lp.ext
  filter_upwards [nativeFlatCollarJet_weak_ae V K,nativeFlatCollarJet_weak_ae V J,hv,hl,hp,
    nativeCollarCutoffCommutator_ae χ hχ J,
    nativeCollarScalarMulCLM_ae χ hχ.continuous (nativeFlatCollarJetCLM V J.val),
    Lp.coeFn_add (nativeCollarScalarMulCLM χ hχ.continuous (nativeFlatCollarJetCLM V J.val))
      (nativeCollarCutoffCommutatorCLM χ hχ J.val)] with x hK hJ hv hl hp hC hM ha
  change nativeFlatCollarJetCLM V K.val x=_
  rw [hK,ha]
  change _=nativeCollarScalarMulCLM χ hχ.continuous (nativeFlatCollarJetCLM V J.val) x+
    nativeCollarCutoffCommutatorCLM χ hχ J.val x
  change weakNegativeLaplacian nativePoissonEntranceCollar K.val.1 x-
    nativeHalfEndPotentialCoefficient V x*K.val.1 x=_
  change weakNegativeLaplacian nativePoissonEntranceCollar K.val.1 x=
    weakNegativeLaplacian nativePoissonEntranceCollar (fun y=>χ y*J.val.1 y) x at hl
  rw [hv,hl,hM,hJ,hC]
  change weakNegativeLaplacian nativePoissonEntranceCollar (fun y=>χ y*J.val.1 y) x-
    χ x*weakNegativeLaplacian nativePoissonEntranceCollar J.val.1 x=
      weakCutoffCommutator nativePoissonEntranceCollar χ J.val.1 x at hp
  linarith only [hp]

#print axioms nativeFlatCollar_cutoff_exact_source
end Yamabe3.Analysis.SpherePolar
