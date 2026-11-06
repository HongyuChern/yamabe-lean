import Yamabe3.Analysis.SpectralL2NeumannTerms

/-! Geometric operator-norm decay of the actual L2 Neumann terms.
The contraction factor comes from both true weighted kernel bounds,
not from a false supremum-potential contraction assertion. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem spectralL2NeumannTerm_enorm_le {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s * |V (t-s)|) ≤ κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s * |V (t-s)|) ≤ κ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) (n : ℕ) :
    ‖spectralL2NeumannTerm k hk₀ hk hδ V n F‖ₑ ≤
      (ENNReal.ofReal κ)^n*ENNReal.ofReal (1/(k₀^2-δ^2))*‖F‖ₑ := by
  let ν := spectralPotentialMeasure V
  let K := spectralPositiveKernel k₀ δ
  let C := ENNReal.ofReal (1/(k₀^2-δ^2))
  letI : SFinite ν := by dsimp [ν,spectralPotentialMeasure]; infer_instance
  have hK : Measurable (Function.uncurry K) := spectralPositiveKernel_measurable k₀ δ
  have hneg : |-δ|<k₀ := by simpa only [abs_neg] using hδ
  have he (x y : ℝ) : K x y=spectralPositiveKernel k₀ (-δ) y x :=
    congrFun (congrFun (spectralPositiveKernel_flip k₀ δ) y) x
  have hrow (x : ℝ) : (∫⁻ y,K x y) ≤ C := (spectralPositiveKernel_row_mass hk₀ hδ x).le
  have hcol (y : ℝ) : (∫⁻ x,K x y) ≤ C := by
    simp_rw [he]
    simpa only [C,neg_sq] using (spectralPositiveKernel_row_mass hk₀ hneg y).le
  have hstep (x : ℝ) : (∫⁻ y,K x y ∂ν) ≤ ENNReal.ofReal κ := by
    rw [spectralPositiveKernel_potential_row hk₀ hδ]
    exact ENNReal.ofReal_le_ofReal (hminus x)
  have hback (y : ℝ) : (∫⁻ x,K x y ∂ν) ≤ ENNReal.ofReal κ := by
    simp_rw [he]
    rw [spectralPositiveKernel_potential_row hk₀ hneg]
    exact ENNReal.ofReal_le_ofReal (hplus y)
  have hsq : ‖spectralL2NeumannTerm k hk₀ hk hδ V n F‖ₑ^2 ≤
      ((ENNReal.ofReal κ)^n*C*‖F‖ₑ)^2 := by
    rw [Lp.enorm_def,eLpNorm_two_sq_eq_lintegral_enorm_sq]
    calc
      _ ≤ ∫⁻ x,(positiveKernelAction volume (positiveKernelPower ν K n)
          (fun s => ‖spectralL2Representative F s‖ₑ) x)^2 := by
        apply lintegral_mono_ae
        filter_upwards [spectralL2NeumannTerm_dominated k hk₀ hk hδ V F n] with x hx
        exact pow_le_pow_left' hx 2
      _ ≤ ((ENNReal.ofReal κ)^n*C)^2*(∫⁻ s,‖spectralL2Representative F s‖ₑ^2) :=
        positiveKernelPower_schur_square volume ν hK hrow hcol hstep hback
          (spectralL2Representative_stronglyMeasurable F).enorm n
      _ = _ := by
        rw [← eLpNorm_two_sq_eq_lintegral_enorm_sq,eLpNorm_congr_ae (spectralL2Representative_ae F),← Lp.enorm_def]
        simp only [mul_pow]
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0:ℝ)<2)).mp
  simpa only [ENNReal.rpow_two] using hsq

theorem spectralL2NeumannTerm_norm_le {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (hκ : 0 ≤ κ) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s * |V (t-s)|) ≤ κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s * |V (t-s)|) ≤ κ)
    (n : ℕ) :
    ‖spectralL2NeumannTerm k hk₀ hk hδ V n‖ ≤ κ^n*(1/(k₀^2-δ^2)) := by
  have hg : 0 ≤ 1/(k₀^2-δ^2) := (one_div_pos.mpr (spectral_gap_positive hk₀ hδ)).le
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (pow_nonneg hκ n) hg)
  intro F
  have hb := spectralL2NeumannTerm_enorm_le k hk₀ hk hδ V hminus hplus F n
  have ht : (ENNReal.ofReal κ)^n*ENNReal.ofReal (1/(k₀^2-δ^2))*‖F‖ₑ ≠ ⊤ := by finiteness
  have hr := ENNReal.toReal_mono ht hb
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal hκ,
    ENNReal.toReal_ofReal hg,toReal_enorm] using hr

#print axioms spectralL2NeumannTerm_enorm_le
#print axioms spectralL2NeumannTerm_norm_le
end Yamabe3.Analysis.Delaunay
