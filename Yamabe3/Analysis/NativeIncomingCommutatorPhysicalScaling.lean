import Yamabe3.Analysis.NativeIncomingCommutatorRepresentative
import Yamabe3.Analysis.DensityCutoffCommutatorScaling

/-! The true physical commutator pairing, with the spectral and weighted
jet powers combined into exactly the three-dimensional Jacobian. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic

theorem nativeIncomingCommutatorSource_normalized_physical_test
    (gE:RiemannianMetric 3 E) (a:ℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (z:RegularLowH4Space) (F:E→ℝ) (hF:ContDiff ℝ ∞ F)
    (he:EqOn (regularLowH4Field z) F (closedBall (0:E) 4))
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ):
    inner ℝ (nativeIncomingCommutatorSourceCLM gE a χ hχ z) (nativePhysicalPairTestL2 φ hφ hc h0)=
      Real.exp (-3*nativeIncomingCutoffSlice.val)*
        (∫y in nativePoissonEntranceCollar,
          densityCutoffCommutator (fun x=>nativeDivergenceMatrix gE (a • x)) χ F
            (Real.exp (-nativeIncomingCutoffSlice.val) • y)*
          φ (Real.exp (-nativeIncomingCutoffSlice.val) • y)):=by
  let s:=nativeIncomingCutoffSlice.val
  let r:=Real.exp (-s)
  let A:E→Matrix (Fin 3) (Fin 3) ℝ:=fun x=>nativeDivergenceMatrix gE (a • x)
  have hA:(fun y=>nativeDivergenceMatrix gE ((a*r) • y))=(fun y=>A (r • y)):=by
    funext y
    simp only [A,smul_smul]
  have hrow:(nativeIncomingCommutatorRowCLM gE a χ hχ z:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      fun y=>(Real.exp (3*s/2)*r^2)*densityCutoffCommutator A χ F (r • y):=by
    have hh:=nativeIncomingCommutatorRow_smooth_ae gE a χ hχ z F hF he
    change (nativeIncomingCommutatorRowCLM gE a χ hχ z:E→ℝ)=ᵐ[_]
      densityCutoffCommutator (fun y=>nativeDivergenceMatrix gE ((a*r) • y))
        (fun y=>χ (r • y)) (fun y=>Real.exp (3*s/2)*F (r • y)) at hh
    rw [hA] at hh
    exact hh.trans (Eventually.of_forall fun y=>densityCutoffCommutator_dilation A χ F r (Real.exp (3*s/2)) y)
  have hcst:Real.exp (-5*s/2)*(Real.exp (3*s/2)*r^2)=Real.exp (-3*s):=by
    dsimp only [r]
    rw [pow_two,←mul_assoc,←Real.exp_add,←mul_assoc,←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  rw [nativeIncomingCommutatorSource_physical_test gE a χ hχ z φ hφ hc h0]
  change Real.exp (-5*s/2)*(∫y in nativePoissonEntranceCollar,
    (nativeIncomingCommutatorRowCLM gE a χ hχ z:E→ℝ) y*φ (r • y))=_
  calc
    _ = Real.exp (-5*s/2)*(∫y in nativePoissonEntranceCollar,
        (Real.exp (3*s/2)*r^2)*(densityCutoffCommutator A χ F (r • y)*φ (r • y))):=by
      congr 1
      apply integral_congr_ae
      filter_upwards [hrow] with y hy
      rw [hy]
      ring
    _ = _:=by
      rw [integral_const_mul,←mul_assoc,hcst]

#print axioms nativeIncomingCommutatorSource_normalized_physical_test
end Yamabe3.Analysis.SpherePolar
