import Yamabe3.Analysis.NativeCutoffCommutatorUniformBound
import Yamabe3.Analysis.RegularLowH4CollarJet
import Yamabe3.Analysis.NativeShiftedFullCollarSourceReturn

/-! The incoming native cutoff source acts on one actual regular-low/H4
field. Its fixed collar is centered at radius 2, within the receiving
core. The real low jets, density divergence, time support and physical
pairing factor are retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay

def nativeIncomingCutoffSlice : HalfEndPhysicalSliceIndex :=
  ⟨-Real.log 2,by have h:0 ≤ Real.log 2 := Real.log_nonneg (by norm_num);linarith⟩

def nativeIncomingCutoffSliceFunction (χ:E→ℝ) : E→ℝ :=
  fun y=>χ (Real.exp (-nativeIncomingCutoffSlice.1) • y)

theorem nativeIncomingCutoffSliceFunction_smooth {χ:E→ℝ} (hχ:ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (nativeIncomingCutoffSliceFunction χ) :=
  hχ.comp (contDiff_id.const_smul _)

def nativeIncomingCommutatorRowCLM (g:RiemannianMetric 3 E) (a:ℝ)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) : RegularLowH4Space →L[ℝ] NativeCollarL2 :=
  (nativeCutoffCommutatorCLM g (a*Real.exp (-nativeIncomingCutoffSlice.1))
    (nativeIncomingCutoffSliceFunction χ) (nativeIncomingCutoffSliceFunction_smooth hχ)).comp
      (regularLowH4ScaleJetCLM nativeIncomingCutoffSlice)

def nativeIncomingCommutatorSourceCLM (g:RiemannianMetric 3 E) (a:ℝ)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) :
    RegularLowH4Space →L[ℝ] Lp AngularSpectralSpace 2 (volume:Measure ℝ) :=
  (nativeShiftedFullCollarSourceReturnCLM nativeIncomingCutoffSlice.1).comp
    (nativeIncomingCommutatorRowCLM g a χ hχ)

theorem exists_nativeIncoming_commutator_source_uniform_bound
    (g:RiemannianMetric 3 E) (hB:g.euclideanCoefficients 0=innerSL ℝ)
    (hρ:g.pullbackVolumeDensity id 0=1) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) :
    ∃C:ℝ,0 < C ∧ ∀a:ℝ,0 ≤ a → a ≤ 1/2 → ‖nativeIncomingCommutatorSourceCLM g a χ hχ‖ ≤ C := by
  obtain ⟨D,hD,hd⟩:=exists_native_cutoff_commutator_uniform_bound (Finset.univ:Finset Unit) (fun _=>g)
    (fun _ _=>hB) (fun _ _=>hρ) (nativeIncomingCutoffSliceFunction χ) (nativeIncomingCutoffSliceFunction_smooth hχ)
  let C:=1+‖nativeShiftedFullCollarSourceReturnCLM nativeIncomingCutoffSlice.1‖*
    D*‖regularLowH4ScaleJetCLM nativeIncomingCutoffSlice‖
  refine ⟨C,by dsimp only [C];positivity,fun a ha ha1=>?_⟩
  have hr:Real.exp (-nativeIncomingCutoffSlice.1)=2 := by
    change Real.exp (-(-Real.log 2))=2
    rw [neg_neg,Real.exp_log (by norm_num:(0:ℝ) < 2)]
  have hA:=hd (a*Real.exp (-nativeIncomingCutoffSlice.1)) (by positivity)
    (by rw [hr];linarith) () (Finset.mem_univ _)
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left
    ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))) (norm_nonneg _)).trans
  dsimp only [C]
  nlinarith [norm_nonneg (nativeShiftedFullCollarSourceReturnCLM nativeIncomingCutoffSlice.1),
    norm_nonneg (regularLowH4ScaleJetCLM nativeIncomingCutoffSlice)]

theorem nativeIncomingCommutatorSource_time_support (g:RiemannianMetric 3 E) (a:ℝ)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (z:RegularLowH4Space) :
    ∀ᵐt:ℝ∂volume,t∉Icc (nativeIncomingCutoffSlice.1-1/2) (nativeIncomingCutoffSlice.1+1/2) →
      nativeIncomingCommutatorSourceCLM g a χ hχ z t=0 :=
  nativeShiftedFullCollarSourceReturn_time_support _ _

theorem nativeIncomingCommutatorSource_physical_test (g:RiemannianMetric 3 E) (a:ℝ)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (z:RegularLowH4Space)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ) :
    inner ℝ (nativeIncomingCommutatorSourceCLM g a χ hχ z) (nativePhysicalPairTestL2 φ hφ hc h0)=
      Real.exp (-5*nativeIncomingCutoffSlice.1/2)*
        (∫y in nativePoissonEntranceCollar,nativeIncomingCommutatorRowCLM g a χ hχ z y*
          φ (Real.exp (-nativeIncomingCutoffSlice.1) • y)) :=
  nativeShiftedFullCollarSourceReturn_physical_test _ _ _ hφ hc h0

#print axioms exists_nativeIncoming_commutator_source_uniform_bound
#print axioms nativeIncomingCommutatorSource_time_support
#print axioms nativeIncomingCommutatorSource_physical_test
end Yamabe3.Analysis.SpherePolar
