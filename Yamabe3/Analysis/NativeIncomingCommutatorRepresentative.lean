import Yamabe3.Analysis.NativeIncomingCommutatorSource
import Yamabe3.Analysis.NativeCollarJetValueInjective

/-! The ACTUAL regular-low/H4 jet is identified with one smooth
representative before evaluating its density-divergence commutator.
All weights and the true radius-two collar remain explicit. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic

theorem regularLowH4ScaleJet_eq_smooth
    (i:HalfEndPhysicalSliceIndex) (z:RegularLowH4Space) (F:E→ℝ)
    (hF:ContDiff ℝ ∞ F) (he:EqOn (regularLowH4Field z) F (closedBall (0:E) 4)):
    regularLowH4ScaleJetCLM i z=nativeC2CollarJetInclusion
      (⟨fun x:E=>Real.exp (3*i.val/2)*F (Real.exp (-i.val) • x),
        (((contDiff_const (c:=Real.exp (3*i.val/2))).mul
          (hF.comp (contDiff_id.const_smul _))).of_le
            (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffOn⟩:nativeC2OffZero):=by
  apply nativeCollarJet_value_injective
  apply Lp.ext
  have hsm:ContDiffOn ℝ 2 (fun x:E=>Real.exp (3*i.val/2)*F (Real.exp (-i.val) • x)) ({0}ᶜ:Set E):=
    (((contDiff_const (c:=Real.exp (3*i.val/2))).mul
      (hF.comp (contDiff_id.const_smul _))).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffOn
  filter_upwards [regularLowH4ScaleJet_value i z,(nativeC2Collar_memLp hsm).1.coeFn_toLp,
    ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hz hf hx
  exact hz.trans ((congrArg (fun t:ℝ=>Real.exp (3*i.val/2)*t)
    (he (halfEnd_physical_slice_mem_entrance_ball i (nativeEntranceCollar_annular hx).2))).trans hf.symm)

theorem nativeIncomingCommutatorRow_smooth_ae
    (gE:RiemannianMetric 3 E) (a:ℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (z:RegularLowH4Space) (F:E→ℝ) (hF:ContDiff ℝ ∞ F)
    (he:EqOn (regularLowH4Field z) F (closedBall (0:E) 4)):
    (nativeIncomingCommutatorRowCLM gE a χ hχ z:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      densityCutoffCommutator
        (fun y=>nativeDivergenceMatrix gE ((a*Real.exp (-nativeIncomingCutoffSlice.val)) • y))
        (nativeIncomingCutoffSliceFunction χ)
        (fun y=>Real.exp (3*nativeIncomingCutoffSlice.val/2)*F (Real.exp (-nativeIncomingCutoffSlice.val) • y)):=by
  change (nativeCutoffCommutatorCLM gE (a*Real.exp (-nativeIncomingCutoffSlice.val))
    (nativeIncomingCutoffSliceFunction χ) (nativeIncomingCutoffSliceFunction_smooth hχ)
      (regularLowH4ScaleJetCLM nativeIncomingCutoffSlice z):E→ℝ)=ᵐ[_]_
  rw [regularLowH4ScaleJet_eq_smooth nativeIncomingCutoffSlice z F hF he]
  exact nativeCutoffCommutatorCLM_C2_ae _ _ _ _ _

#print axioms regularLowH4ScaleJet_eq_smooth
#print axioms nativeIncomingCommutatorRow_smooth_ae
end Yamabe3.Analysis.SpherePolar
