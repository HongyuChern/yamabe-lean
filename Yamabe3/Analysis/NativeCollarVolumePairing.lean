import Yamabe3.Analysis.NativeCollarJetSpace

/-! Actual continuous L2 test pairing on measurable collar regions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic

private theorem collar_test_memLp (φ : E → ℝ) (hφ : Continuous φ) :
    MemLp φ 2 (volume.restrict nativePoissonEntranceCollar) :=
  native_memLp_two_of_continuousOn_precompact (nativePolarTimeWindow_open (1/2)).measurableSet
    (nativePolarTimeWindow_precompact (1/2)) (nativePolarTimeWindow_closure_offZero (1/2)) hφ.continuousOn

def nativeCollarRegionTestLp (s : Set E) (hs : MeasurableSet s) (φ : E → ℝ) (hφ : Continuous φ) : NativeCollarL2 :=
  ((collar_test_memLp φ hφ).indicator hs).toLp (s.indicator φ)

def nativeCollarVolumePairCLM (s : Set E) (hs : MeasurableSet s) (φ : E → ℝ) (hφ : Continuous φ) :
    NativeCollarL2 →L[ℝ] ℝ := innerSL ℝ (nativeCollarRegionTestLp s hs φ hφ)

theorem nativeCollarVolumePair_eq_integral (s : Set E) (hs : MeasurableSet s)
    (φ : E → ℝ) (hφ : Continuous φ) (F : NativeCollarL2) :
    nativeCollarVolumePairCLM s hs φ hφ F=
      ∫ x in nativePoissonEntranceCollar ∩ s,φ x*(F : E → ℝ) x := by
  change inner ℝ (nativeCollarRegionTestLp s hs φ hφ) F=_
  rw [L2.inner_def]
  have ht : (nativeCollarRegionTestLp s hs φ hφ : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      s.indicator φ := MemLp.coeFn_toLp _
  calc
    _ = ∫ x,s.indicator (fun x => φ x*(F : E → ℝ) x) x ∂volume.restrict nativePoissonEntranceCollar := by
      apply integral_congr_ae
      filter_upwards [ht] with x hx
      simp only [RCLike.inner_apply,conj_trivial,hx]
      by_cases hxs : x∈s
      · simp only [indicator_of_mem hxs];ring
      · simp only [indicator_of_notMem hxs,mul_zero]
    _ = ∫ x,φ x*(F : E → ℝ) x ∂(volume.restrict nativePoissonEntranceCollar).restrict s := integral_indicator hs
    _ = _ := by rw [Measure.restrict_restrict hs,inter_comm]

#print axioms nativeCollarVolumePair_eq_integral
end Yamabe3.Analysis.SpherePolar
