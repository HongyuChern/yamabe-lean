import Yamabe3.Analysis.SpectralL2PotentialContinuous

/-! Actual scalar-coordinate L2 test pairings as continuous linear maps. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay

def spectralL2TestCLM {ι : Type*} (i : ι) (φ : ℝ → ℝ) (hφ : MemLp φ 2) :
    Lp (SpectralSpace ι) 2 (volume : Measure ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (hφ.toLp φ)).comp ((lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i).compLpL 2 volume)

theorem spectralL2TestCLM_apply {ι : Type*} (i : ι) (φ : ℝ → ℝ) (hφ : MemLp φ 2)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    spectralL2TestCLM i φ hφ F=∫ t : ℝ,φ t*F t i := by
  change inner ℝ (hφ.toLp φ) ((lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i).compLp F)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp,(lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i).coeFn_compLp F] with t ht hf
  simp only [ht,hf,Real.inner_apply,mul_comm]
  rfl

theorem spectralL2TestCLM_apply_ae {ι : Type*} (i : ι) (φ : ℝ → ℝ) (hφ : MemLp φ 2)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) (W : ℝ → SpectralSpace ι)
    (hFW : (F : ℝ → SpectralSpace ι)=ᵐ[volume] W) :
    spectralL2TestCLM i φ hφ F=∫ t : ℝ,φ t*W t i := by
  rw [spectralL2TestCLM_apply]
  exact integral_congr_ae (hFW.mono (fun t ht => congrArg (fun x : SpectralSpace ι => φ t*x i) ht))

#print axioms spectralL2TestCLM_apply
#print axioms spectralL2TestCLM_apply_ae
end Yamabe3.Analysis.Delaunay
