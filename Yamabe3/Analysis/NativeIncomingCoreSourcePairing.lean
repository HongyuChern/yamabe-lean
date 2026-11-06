import Yamabe3.Analysis.NativeCoreUnitOperator
import Yamabe3.Analysis.NativeIncomingCommutatorPhysicalScaling

/-! Exact identification of the incoming cutoff source as the NEGATIVE
normalized core operator source, including the three-dimensional volume
Jacobian. The support proof extends the true collar integral globally. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

theorem nativeIncomingCommutatorSource_eq_negative_core_test
    (gE:RiemannianMetric 3 E) (a:ℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (hs:tsupport χ⊆ball (0:E) 3)
    (h1:∀x∈closedBall (0:E) 2,χ=ᶠ[𝓝 x](fun _=>1))
    (z:RegularLowH4Space) (F:E→ℝ) (hF:ContDiff ℝ ∞ F)
    (he:EqOn (regularLowH4Field z) F (closedBall (0:E) 4))
    (hzero:∀x∈closedBall (0:E) 4,
      principalSource (fun y=>nativeDivergenceMatrix gE (a • y)) F x+
        a^2*nativePotentialDensity gE (a • x)*F x=0)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ):
    inner ℝ (nativeIncomingCommutatorSourceCLM gE a χ hχ z) (nativePhysicalPairTestL2 φ hφ hc h0)=
      -(∫x:E,nativeCoreUnitOperator gE a χ F x*φ x):=by
  have he0:Real.exp (-nativeIncomingCutoffSlice.val)=2:=by
    change Real.exp (-(-Real.log 2))=2
    rw [neg_neg,Real.exp_log (by norm_num:(0:ℝ)<2)]
  have he3:Real.exp (-3*nativeIncomingCutoffSlice.val)=8:=by
    have hh:Real.exp (-3*nativeIncomingCutoffSlice.val)=(Real.exp (-nativeIncomingCutoffSlice.val))^3:=by
      rw [←Real.exp_nat_mul]
      congr 1
      ring
    rw [hh,he0]
    norm_num
  let H:=nativeCoreUnitOperator gE a χ F
  let D: Set E:=(fun x:E=>(1/2:ℝ) • x) ⁻¹' nativePoissonEntranceCollar
  have hcomm(x:E):densityCutoffCommutator (fun y=>nativeDivergenceMatrix gE (a • y)) χ F x= -H x:=by
    have hh:=nativeCoreUnitOperator_eq_negative_commutator gE a χ F hχ hF hs hzero x
    dsimp only [H]
    linarith only [hh]
  have hd:(∫x in D,H x*φ x)=8*(∫y in nativePoissonEntranceCollar,H ((2:ℝ) • y)*φ ((2:ℝ) • y)):=by
    have hh:=setIntegral_comp_dilation (r:=(1/2:ℝ)) (by norm_num) nativePoissonEntranceCollar
      (fun y:E=>H ((2:ℝ) • y)*φ ((2:ℝ) • y))
    norm_num only [finrank_euclideanSpace_fin,inv_pow,one_div] at hh
    simpa only [smul_smul,show (2:ℝ)*(1/2)=1 by norm_num,one_smul] using hh
  rw [nativeIncomingCommutatorSource_normalized_physical_test gE a χ hχ z F hF he φ hφ hc h0,he3,he0]
  calc
    _ = 8*(∫y in nativePoissonEntranceCollar,-(H ((2:ℝ) • y)*φ ((2:ℝ) • y))):=by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun y=>by
        change densityCutoffCommutator (fun x=>nativeDivergenceMatrix gE (a • x)) χ F ((2:ℝ) • y)*φ ((2:ℝ) • y)=_
        rw [hcomm]
        ring
    _ = -(8*(∫y in nativePoissonEntranceCollar,H ((2:ℝ) • y)*φ ((2:ℝ) • y))):=by rw [integral_neg];ring
    _ = -(∫x in D,H x*φ x):=congrArg Neg.neg hd.symm
    _ = _:=by
      congr 1
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      change nativeCoreUnitOperator gE a χ F x*φ x=0
      rw [nativeCoreUnitOperator_zero_off_incoming gE a χ F hs h1 hzero hx,zero_mul]

#print axioms nativeIncomingCommutatorSource_eq_negative_core_test
end Yamabe3.Analysis.SpherePolar
