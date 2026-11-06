import Yamabe3.Analysis.SpectralL2KernelDomination
import Yamabe3.Analysis.PositiveKernelPowerBound

/-! Actual L2 Neumann terms and domination by the same iterated kernels.
The negative free Green kernel and the minus-potential fixed point keep
the original signs; only norms use the positive majorant. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

def spectralL2NeumannTerm {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (V : ℝ →ᵇ ℝ) :
    ℕ → (Lp (SpectralSpace ι) 2 (volume : Measure ℝ) →L[ℝ] Lp (SpectralSpace ι) 2 (volume : Measure ℝ))
  | 0 => spectralL2FreeCLM k hk₀ hk hδ
  | n+1 => -((spectralL2FreeCLM k hk₀ hk hδ).comp
      ((spectralL2PotentialMulCLM V).comp (spectralL2NeumannTerm k hk₀ hk hδ V n)))

theorem spectralL2NeumannTerm_dominated {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (V : ℝ →ᵇ ℝ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) (n : ℕ) :
    ∀ᵐ t : ℝ,‖(spectralL2NeumannTerm k hk₀ hk hδ V n F : ℝ → SpectralSpace ι) t‖ₑ ≤
      positiveKernelAction volume
        (positiveKernelPower (spectralPotentialMeasure V) (spectralPositiveKernel k₀ δ) n)
        (fun s => ‖spectralL2Representative F s‖ₑ) t := by
  let ν := spectralPotentialMeasure V
  let K := spectralPositiveKernel k₀ δ
  let f := fun s => ‖spectralL2Representative F s‖ₑ
  letI : SFinite ν := by dsimp [ν,spectralPotentialMeasure]; infer_instance
  have hK : Measurable (Function.uncurry K) := spectralPositiveKernel_measurable k₀ δ
  have hf : Measurable f := (spectralL2Representative_stronglyMeasurable F).enorm
  induction n with
  | zero =>
    have hid (t : ℝ) : positiveKernelAction volume K (fun s => ‖F s‖ₑ) t=positiveKernelAction volume K f t := by
      apply lintegral_congr_ae
      filter_upwards [spectralL2Representative_ae F] with s hs
      dsimp only [f]
      rw [hs]
    filter_upwards [spectralL2FreeCLM_enorm_ae k hk₀ hk hδ F] with t ht
    change _ ≤ positiveKernelAction volume K f t
    rw [← hid]
    exact ht
  | succ n ih =>
    let U := spectralL2NeumannTerm k hk₀ hk hδ V n F
    let Z := spectralL2FreeCLM k hk₀ hk hδ (spectralL2PotentialMulCLM V U)
    have ihν : ∀ᵐ s ∂ν,‖U s‖ₑ ≤ positiveKernelAction volume (positiveKernelPower ν K n) f s :=
      (withDensity_absolutelyContinuous volume (fun s => ENNReal.ofReal |V s|)).ae_le ih
    have hb (t : ℝ) : positiveKernelAction ν K (fun s => ‖U s‖ₑ) t ≤
        positiveKernelAction volume (positiveKernelPower ν K (n+1)) f t := by
      calc
        _ ≤ positiveKernelAction ν K (positiveKernelAction volume (positiveKernelPower ν K n) f) t := by
          apply lintegral_mono_ae
          filter_upwards [ihν] with s hs
          gcongr
        _ = _ := congrFun (positiveKernelAction_comp volume ν hK (positiveKernelPower_measurable ν hK n) hf) t
    filter_upwards [spectralL2FreePotential_enorm_ae k hk₀ hk hδ V U,Lp.coeFn_neg Z] with t ht hz
    change ‖((-Z : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) : ℝ → SpectralSpace ι) t‖ₑ ≤ _
    rw [hz]
    simp only [Pi.neg_apply,enorm_neg]
    exact ht.trans (hb t)

#print axioms spectralL2NeumannTerm_dominated
end Yamabe3.Analysis.Delaunay
