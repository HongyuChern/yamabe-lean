import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! A reusable closed-property extension from the actual dense
bounded-continuous representatives that belong to L2. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BoundedContinuousFunction
namespace Yamabe3.Analysis

theorem continuous_L2_eq_of_boundedContinuous_sources
    {H Y : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace Y] [T2Space Y]
    {f g : Lp H 2 (volume : Measure ℝ) → Y} (hf : Continuous f) (hg : Continuous g)
    (he : ∀ F : ℝ →ᵇ H, ∀ hF : MemLp (F : ℝ → H) 2 (volume : Measure ℝ), f (hF.toLp F)=g (hF.toLp F)) : f=g := by
  apply hf.ext_on (Lp.boundedContinuousFunction_dense H volume (by norm_num : (2:ℝ≥0∞)≠⊤)) hg
  intro F hF
  obtain ⟨W,hW⟩ := Lp.mem_boundedContinuousFunction_iff.mp hF
  have hae : (F : ℝ → H)=ᵐ[volume] W := by
    change ((F : ℝ →ₘ[volume] H) : ℝ → H)=ᵐ[volume] W
    rw [←hW]
    exact W.toContinuousMap.coeFn_toAEEqFun volume
  have hw2 : MemLp (W : ℝ → H) 2 (volume : Measure ℝ) := (Lp.memLp F).ae_eq hae
  have hid : hw2.toLp W=F := by
    apply Lp.ext
    exact hw2.coeFn_toLp.trans hae.symm
  simpa only [hid] using he W hw2

#print axioms continuous_L2_eq_of_boundedContinuous_sources
end Yamabe3.Analysis
