import Yamabe3.Analysis.SpectralL2FixedPointUnique

/-! The literal affine iteration from zero converges in L2 to the new
operator, by its actual Neumann series, despite no one-step norm gap. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

def spectralL2PotentialIteration {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (V : ℝ →ᵇ ℝ)
    (F U : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) : Lp (SpectralSpace ι) 2 (volume : Measure ℝ) :=
  spectralL2FreeCLM k hk₀ hk hδ (F-spectralL2PotentialMulCLM V U)

theorem spectralL2PotentialIteration_eq_sum {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (V : ℝ →ᵇ ℝ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) (n : ℕ) :
    (spectralL2PotentialIteration k hk₀ hk hδ V F)^[n] 0=
      ∑ i ∈ Finset.range n,spectralL2NeumannTerm k hk₀ hk hδ V i F := by
  let R := spectralL2FreeCLM k hk₀ hk hδ
  let M := spectralL2PotentialMulCLM (ι := ι) V
  let T := spectralL2NeumannTerm k hk₀ hk hδ V
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,Finset.sum_range_succ',add_comm]
    change R (F-M (∑ i ∈ Finset.range n,T i F))=T 0 F+∑ i ∈ Finset.range n,T (i+1) F
    rw [map_sub,map_sum,map_sum]
    change R F-(∑ i ∈ Finset.range n,R (M (T i F)))=R F+∑ i ∈ Finset.range n,-R (M (T i F))
    rw [Finset.sum_neg_distrib,sub_eq_add_neg]

theorem spectralL2PotentialIteration_tendsto {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (hκ0 : 0 ≤ κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s * |V (t-s)|) ≤ κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s * |V (t-s)|) ≤ κ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    Tendsto (fun n : ℕ => (spectralL2PotentialIteration k hk₀ hk hδ V F)^[n] 0) atTop
      (𝓝 (spectralL2IntegralPotentialInverse k hk₀ hk hδ V F)) := by
  have hs := spectralL2NeumannTerm_summable k hk₀ hk hδ hκ0 hκ1 V hminus hplus
  let ev := ContinuousLinearMap.apply ℝ (Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) F
  have ht := (ev.hasSum hs.hasSum).tendsto_sum_nat
  simpa only [spectralL2PotentialIteration_eq_sum,ev,ContinuousLinearMap.apply_apply,
    spectralL2IntegralPotentialInverse] using ht

#print axioms spectralL2PotentialIteration_eq_sum
#print axioms spectralL2PotentialIteration_tendsto
end Yamabe3.Analysis.Delaunay
