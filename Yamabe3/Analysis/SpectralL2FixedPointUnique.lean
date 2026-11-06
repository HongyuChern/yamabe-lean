import Yamabe3.Analysis.SpectralL2IntegralPotentialInverse

/-! Uniqueness in the full L2 space follows from the proved geometric
bound on the actual iterated resolvents; no one-step contraction claim
is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem spectralL2_potential_homogeneous_zero {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (hκ0 : 0 ≤ κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s * |V (t-s)|) ≤ κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s * |V (t-s)|) ≤ κ)
    (U : Lp (SpectralSpace ι) 2 (volume : Measure ℝ))
    (hU : U= -spectralL2FreeCLM k hk₀ hk hδ (spectralL2PotentialMulCLM V U)) : U=0 := by
  let R := spectralL2FreeCLM k hk₀ hk hδ
  let M := spectralL2PotentialMulCLM (ι := ι) V
  let T := spectralL2NeumannTerm k hk₀ hk hδ V
  have hn (n : ℕ) : U= -T n (M U) := by
    induction n with
    | zero => exact hU
    | succ n ih =>
      have ht : T n (M U)= -U := by simpa only [neg_neg] using (congrArg Neg.neg ih).symm
      change U= -(-R (M (T n (M U))))
      rw [neg_neg,ht,map_neg,map_neg]
      exact hU
  have hb (n : ℕ) : ‖U‖ ≤ (κ^n*(1/(k₀^2-δ^2)))*‖M U‖ := by
    calc
      ‖U‖ = ‖T n (M U)‖ := by simpa only [norm_neg] using congrArg norm (hn n)
      _ ≤ ‖T n‖*‖M U‖ := (T n).le_opNorm (M U)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (spectralL2NeumannTerm_norm_le k hk₀ hk hδ hκ0 V hminus hplus n) (norm_nonneg (M U))
  have ht : Tendsto (fun n : ℕ => (κ^n*(1/(k₀^2-δ^2)))*‖M U‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).mul_const (1/(k₀^2-δ^2))).mul_const ‖M U‖
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto ht (Eventually.of_forall hb)) (norm_nonneg U))

theorem spectralL2IntegralPotentialInverse_unique {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (hκ0 : 0 ≤ κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s * |V (t-s)|) ≤ κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s * |V (t-s)|) ≤ κ)
    (F U : Lp (SpectralSpace ι) 2 (volume : Measure ℝ))
    (hU : U=spectralL2FreeCLM k hk₀ hk hδ (F-spectralL2PotentialMulCLM V U)) :
    U=spectralL2IntegralPotentialInverse k hk₀ hk hδ V F := by
  let Z := spectralL2IntegralPotentialInverse k hk₀ hk hδ V F
  let R := spectralL2FreeCLM k hk₀ hk hδ
  let M := spectralL2PotentialMulCLM (ι := ι) V
  have hZ : Z=R (F-M Z) := spectralL2IntegralPotentialInverse_fixed k hk₀ hk hδ hκ0 hκ1 V hminus hplus F
  have hdiff : U-Z= -R (M (U-Z)) := by
    calc
      _ = R (F-M U)-R (F-M Z) := congrArg₂ (·-·) hU hZ
      _ = R ((F-M U)-(F-M Z)) := (map_sub R _ _).symm
      _ = -R (M (U-Z)) := by
        rw [map_sub M,← map_neg R]
        congr 1
        abel
  exact sub_eq_zero.mp (spectralL2_potential_homogeneous_zero k hk₀ hk hδ hκ0 hκ1 V hminus hplus (U-Z) hdiff)

#print axioms spectralL2_potential_homogeneous_zero
#print axioms spectralL2IntegralPotentialInverse_unique
end Yamabe3.Analysis.Delaunay
