import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Strong L2 convergence and AE pointwise convergence of the SAME
representatives identify their limits. No L2 membership of the desired
pointwise limit is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Yamabe3.Analysis

theorem ae_eq_of_tendsto_Lp_of_ae_pointwise
    {α:Type*} [MeasurableSpace α] {μ:Measure α}
    (z:ℕ→Lp ℝ 2 μ) (Z:Lp ℝ 2 μ) (hz:Tendsto z atTop (𝓝 Z))
    (u:ℕ→α→ℝ) (U:α→ℝ) (hrep:∀n,u n=ᵐ[μ](z n:α→ℝ))
    (hpoint:∀ᵐx∂μ,Tendsto (fun n=>u n x) atTop (𝓝 (U x))) :
    U=ᵐ[μ](Z:α→ℝ) := by
  obtain ⟨σ,hσ,hsub⟩:=(tendstoInMeasure_of_tendsto_Lp hz).exists_seq_tendsto_ae
  have hall:∀ᵐx∂μ,∀n,u n x=z n x := ae_all_iff.mpr hrep
  filter_upwards [hall,hpoint,hsub] with x hx hp hs
  have he:(fun n=>u (σ n) x)=(fun n=>z (σ n) x) := funext (fun n=>hx (σ n))
  have ht:=hp.comp hσ.tendsto_atTop
  change Tendsto (fun n=>u (σ n) x) atTop (𝓝 (U x)) at ht
  rw [he] at ht
  exact tendsto_nhds_unique ht hs

#print axioms ae_eq_of_tendsto_Lp_of_ae_pointwise
end Yamabe3.Analysis
