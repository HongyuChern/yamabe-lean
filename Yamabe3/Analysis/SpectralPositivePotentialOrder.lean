import Yamabe3.Analysis.SpectralIntegralLinearity

/-!
# The sign of the same integral-small nonnegative-potential inverse

The actual free Green kernel is negative. For a nonnegative common
potential, every true Banach iterate for a nonnegative source coordinate
is nonpositive, and this property passes to the same Hilbert fixed point.
The integrated smallness assumption remains exactly 0 <= kappa < 1.
This sign will invert the entrance diagonal without imposing kappa < 1/2.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter MeasureTheory
open scoped Topology lp BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

theorem spectralResolvent_coordinate_nonpos_of_nonneg_source
    {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F : ℝ →ᵇ SpectralSpace ι) (i : ι) (hF : ∀ t, 0 ≤ F t i) (t : ℝ) :
    spectralResolventCLM k hk₀ hk hδ F t i ≤ 0 := by
  let ev := lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i
  have hi := spectralConvolution_integrable k hk₀ hk hδ F t
  change ev (∫ s : ℝ, weightedSpectralKernel k hk₀ hk δ s (F (t - s))) ≤ 0
  rw [← ev.integral_comp_comm hi]
  apply integral_nonpos
  intro s
  change Real.exp (-δ * s) * (scalarGreenKernel (k i) s * F (t - s) i) ≤ 0
  apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
  apply mul_nonpos_of_nonpos_of_nonneg _ (hF _)
  unfold scalarGreenKernel
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le)
    (by have := hk i; linarith)

/-- Sign reversal is proved for the actual canonical Hilbert fixed point,
with the same integrated smallness criterion used by the accepted inverse. -/
theorem spectralIntegralPotentialInverse_coordinate_nonpos
    {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ)
    (hV0 : ∀ t, 0 ≤ V t) (F : ℝ →ᵇ SpectralSpace ι)
    (i : ι) (hF : ∀ t, 0 ≤ F t i) (t : ℝ) :
    spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F t i ≤ 0 := by
  let A := spectralPotentialIteration k hk₀ hk hδ V F
  have hc := spectralPotentialIteration_integral_contracting k hk₀ hk hδ hκ0 hκ1 V hV F
  have hn (n : ℕ) : ∀ s, (A^[n] 0) s i ≤ 0 := by
    induction n with
    | zero => intro s; exact le_rfl
    | succ n ih =>
      intro s
      rw [Function.iterate_succ_apply']
      change spectralResolventCLM k hk₀ hk hδ (F - V • (A^[n] 0)) s i ≤ 0
      apply spectralResolvent_coordinate_nonpos_of_nonneg_source k hk₀ hk hδ _ i _ s
      intro x
      change 0 ≤ F x i - V x * (A^[n] 0) x i
      have hprod := mul_nonpos_of_nonneg_of_nonpos (hV0 x) (ih x)
      linarith only [hF x, hprod]
  have hev : Continuous (fun H : ℝ →ᵇ SpectralSpace ι => H t i) :=
    (lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i).continuous.comp
      (BoundedContinuousFunction.evalCLM (𝕜 := ℝ) t).continuous
  have hlim := hev.continuousAt.tendsto.comp (hc.tendsto_iterate_fixedPoint 0)
  exact le_of_tendsto hlim (Eventually.of_forall (fun n => hn n t))

/-- Applying the same inverse to V times a curve uses the actual integral
smallness kappa, without replacing it by the potential supremum. -/
theorem spectralIntegralPotentialInverse_potential_source_norm_le
    {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ δ s * |V (t - s)|) ≤ κ)
    (U : ℝ →ᵇ SpectralSpace ι) :
    ‖spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV (V • U)‖ ≤
      (κ / (1 - κ)) * ‖U‖ := by
  let w := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV (V • U)
  have hfixed := spectralIntegralPotentialInverse_fixed k hk₀ hk hδ hκ0 hκ1 V hV (V • U)
  have heq : V • U - V • w = V • (U - w) := by
    apply BoundedContinuousFunction.ext
    intro t
    change V t • U t - V t • w t = V t • (U t - w t)
    rw [smul_sub]
  have hn : ‖w‖ ≤ κ * (‖U‖ + ‖w‖) := by
    calc
      _ = ‖spectralResolventCLM k hk₀ hk hδ (V • (U - w))‖ := by
        rw [← heq]
        exact congrArg norm hfixed.symm
      _ ≤ κ * ‖U - w‖ := spectralResolvent_potential_norm_le k hk₀ hk hδ hκ0 V hV _
      _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sub_le U w) hκ0
  have h : ‖w‖ ≤ (κ * ‖U‖) / (1 - κ) := by
    apply (le_div_iff₀ (sub_pos.mpr hκ1)).mpr
    nlinarith only [hn]
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm ‖U‖] using h

#print axioms spectralResolvent_coordinate_nonpos_of_nonneg_source
#print axioms spectralIntegralPotentialInverse_coordinate_nonpos
#print axioms spectralIntegralPotentialInverse_potential_source_norm_le

end Yamabe3.Analysis.Delaunay
