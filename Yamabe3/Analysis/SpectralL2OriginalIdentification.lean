import Yamabe3.Analysis.SpectralL2IterationLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! The newly constructed L2 inverse and the original continuous inverse
are the same solution on their common source domain. Equality follows
from the literal common iterations and an a.e. converging subsequence;
no L2 membership of the old solution is inserted as an assumption. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem spectralL2FreeCLM_agrees_ae {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) (H : ℝ →ᵇ SpectralSpace ι)
    (hFH : (F : ℝ → SpectralSpace ι)=ᵐ[volume] H) :
    (spectralL2FreeCLM k hk₀ hk hδ F : ℝ → SpectralSpace ι)=ᵐ[volume]
      spectralResolventCLM k hk₀ hk hδ H := by
  have h := spectralL2Resolvent_coe_ae k hk₀ hk hδ F
  rw [spectralL2Convolution_congr_ae k hk₀ hk δ hFH] at h
  filter_upwards [h] with t ht
  exact ht.trans (spectralL2Convolution_eq_original k hk₀ hk δ H t)

theorem spectralL2PotentialIteration_agrees_ae {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (V : ℝ →ᵇ ℝ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) (H : ℝ →ᵇ SpectralSpace ι)
    (hFH : (F : ℝ → SpectralSpace ι)=ᵐ[volume] H) (n : ℕ) :
    ((spectralL2PotentialIteration k hk₀ hk hδ V F)^[n] 0 : ℝ → SpectralSpace ι)=ᵐ[volume]
      (spectralPotentialIteration k hk₀ hk hδ V H)^[n] 0 := by
  induction n with
  | zero => exact Lp.coeFn_zero _ _ _
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    apply spectralL2FreeCLM_agrees_ae
    filter_upwards [hFH,ih,
      Lp.coeFn_sub F (spectralL2PotentialMulCLM V ((spectralL2PotentialIteration k hk₀ hk hδ V F)^[n] 0)),
      spectralL2PotentialMul_coe_ae V ((spectralL2PotentialIteration k hk₀ hk hδ V F)^[n] 0)] with t hf hu hs hm
    change (F-spectralL2PotentialMulCLM V ((spectralL2PotentialIteration k hk₀ hk hδ V F)^[n] 0)) t =
      H t-V t • ((spectralPotentialIteration k hk₀ hk hδ V H)^[n] 0) t
    change (spectralL2PotentialMulCLM V ((spectralL2PotentialIteration k hk₀ hk hδ V F)^[n] 0)) t =
      V t • ((spectralL2PotentialIteration k hk₀ hk hδ V F)^[n] 0) t at hm
    simpa only [Pi.sub_apply,hs,hm,hf,hu]

theorem spectralL2IntegralPotentialInverse_agrees_original {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (hκ0 : 0 ≤ κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s * |V (t-s)|) ≤ κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s * |V (t-s)|) ≤ κ)
    (F : ℝ →ᵇ SpectralSpace ι) (hF : MemLp F 2) :
    (spectralL2IntegralPotentialInverse k hk₀ hk hδ V (hF.toLp F) : ℝ → SpectralSpace ι)=ᵐ[volume]
      spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hminus F := by
  let z := fun n => (spectralL2PotentialIteration k hk₀ hk hδ V (hF.toLp F))^[n] 0
  let u := fun n => (spectralPotentialIteration k hk₀ hk hδ V F)^[n] 0
  have hz := spectralL2PotentialIteration_tendsto k hk₀ hk hδ hκ0 hκ1 V hminus hplus (hF.toLp F)
  obtain ⟨σ,hσ,hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hz).exists_seq_tendsto_ae
  have hrep : ∀ᵐ t ∂volume, ∀ n, z n t=u n t :=
    ae_all_iff.mpr (fun n => spectralL2PotentialIteration_agrees_ae k hk₀ hk hδ V (hF.toLp F) F hF.coeFn_toLp n)
  have hc := spectralPotentialIteration_integral_contracting k hk₀ hk hδ hκ0 hκ1 V hminus F
  filter_upwards [hrep,hsub] with t ht hs
  have hp := (BoundedContinuousFunction.evalCLM ℝ t).continuous.continuousAt.tendsto.comp
    (hc.tendsto_iterate_fixedPoint 0)
  have he : (fun n => z (σ n) t)=(fun n => u (σ n) t) := funext fun n => ht (σ n)
  change Tendsto (fun n => z (σ n) t) atTop _ at hs
  rw [he] at hs
  exact tendsto_nhds_unique hs (hp.comp hσ.tendsto_atTop)

theorem spectralIntegralPotentialInverse_memLp {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (hκ0 : 0 ≤ κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s * |V (t-s)|) ≤ κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s * |V (t-s)|) ≤ κ)
    (F : ℝ →ᵇ SpectralSpace ι) (hF : MemLp F 2) :
    MemLp (spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hminus F) 2 :=
  (Lp.memLp _).ae_eq (spectralL2IntegralPotentialInverse_agrees_original k hk₀ hk hδ hκ0 hκ1 V hminus hplus F hF)

#print axioms spectralL2PotentialIteration_agrees_ae
#print axioms spectralL2IntegralPotentialInverse_agrees_original
#print axioms spectralIntegralPotentialInverse_memLp
end Yamabe3.Analysis.Delaunay
