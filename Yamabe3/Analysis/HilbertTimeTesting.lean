import Yamabe3.Analysis.TimeTestEquation
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# From genuine Hilbert coefficient equations to angular weak tests

Time integration is an actual Bochner integral. A Hilbert-basis Parseval
identity transfers the integrated coefficient equations to every angular
test whose actual operator image has the proved spectral coefficients.
No exchange of a spectral sum with a time supremum is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def timeBochnerPair (ζ : ℝ → ℝ) (U : ℝ → H) : H := ∫ t : ℝ, ζ t • U t

omit [CompleteSpace H] in
theorem timeBochnerPair_integrable {ζ : ℝ → ℝ} {U : ℝ → H}
    (hζ : Continuous ζ) (hc : HasCompactSupport ζ) (hU : Continuous U) :
    Integrable (fun t : ℝ => ζ t • U t) :=
  (hζ.smul hU).integrable_of_hasCompactSupport hc.smul_right

theorem inner_timeBochnerPair {ζ : ℝ → ℝ} {U : ℝ → H}
    (hζ : Continuous ζ) (hc : HasCompactSupport ζ) (hU : Continuous U) (x : H) :
    inner ℝ x (timeBochnerPair ζ U) = ∫ t : ℝ, ζ t * inner ℝ x (U t) := by
  change (innerSL ℝ x) (∫ t : ℝ, ζ t • U t) = _
  rw [← (innerSL ℝ x).integral_comp_comm (timeBochnerPair_integrable hζ hc hU)]
  simp only [innerSL_apply_apply, real_inner_smul_right]

omit [CompleteSpace H] in
/-- Parseval identifies the weak operator relation without asserting an
unproved pointwise operator on the Hilbert-valued solution. -/
theorem inner_eq_of_spectral_relation (b : HilbertBasis ι ℝ H) (μ : ι → ℝ)
    {B W x Ax : H}
    (hB : ∀ i, inner ℝ (b i) B = μ i * inner ℝ (b i) W)
    (hAx : ∀ i, inner ℝ (b i) Ax = μ i * inner ℝ (b i) x) :
    inner ℝ x B = inner ℝ Ax W := by
  rw [← b.tsum_inner_mul_inner x B, ← b.tsum_inner_mul_inner Ax W]
  apply tsum_congr
  intro i
  rw [real_inner_comm (b i) x, real_inner_comm (b i) Ax, hB, hAx]
  ring

/-- Actual time-tested equation for every angular test with its true
spectral operator image. The coefficient equations are consumed, not
repackaged into the conclusion. -/
theorem hilbert_compact_time_test (b : HilbertBasis ι ℝ H) (μ : ι → ℝ)
    {U F : ℝ → H} {V : ℝ → ℝ} {a₀ β : ℝ}
    (hU : Continuous U) (hF : Continuous F) (hV : Continuous V)
    (hUs : ∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (b i) (U t)))
    (heq : ∀ i t, deriv (deriv (fun s => inner ℝ (b i) (U s))) t =
      β * deriv (fun s => inner ℝ (b i) (U s)) t +
        (μ i + a₀) * inner ℝ (b i) (U t) + inner ℝ (b i) (F t) -
          V t * inner ℝ (b i) (U t))
    {ζ : ℝ → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ)
    (x Ax : H) (hAx : ∀ i, inner ℝ (b i) Ax = μ i * inner ℝ (b i) x) :
    (∫ t : ℝ, deriv (deriv ζ) t * inner ℝ x (U t)) +
      β * (∫ t : ℝ, deriv ζ t * inner ℝ x (U t)) -
      a₀ * (∫ t : ℝ, ζ t * inner ℝ x (U t)) +
      (∫ t : ℝ, ζ t * V t * inner ℝ x (U t)) -
      (∫ t : ℝ, ζ t * inner ℝ Ax (U t)) =
        ∫ t : ℝ, ζ t * inner ℝ x (F t) := by
  have hdζ := (contDiff_infty_iff_deriv.mp hζ).2
  have hddζ := (contDiff_infty_iff_deriv.mp hdζ).2
  have hζV : Continuous (fun t => ζ t * V t) := hζ.continuous.mul hV
  have hcζV : HasCompactSupport (fun t => ζ t * V t) := hc.mul_right
  let W := timeBochnerPair ζ U
  let B := timeBochnerPair (deriv (deriv ζ)) U + β • timeBochnerPair (deriv ζ) U -
    a₀ • W + timeBochnerPair (fun t => ζ t * V t) U - timeBochnerPair ζ F
  have hB (i : ι) : inner ℝ (b i) B = μ i * inner ℝ (b i) W := by
    have hs := second_order_compact_time_test hζ hc (hUs i) hV
      ((innerSL ℝ (b i)).continuous.comp hF) (heq i)
    simp only [Function.comp_apply, innerSL_apply_apply] at hs
    dsimp [B, W]
    rw [inner_sub_right, inner_add_right, inner_sub_right, inner_add_right,
      real_inner_smul_right, real_inner_smul_right,
      inner_timeBochnerPair hddζ.continuous hc.deriv.deriv hU,
      inner_timeBochnerPair hdζ.continuous hc.deriv hU,
      inner_timeBochnerPair hζ.continuous hc hU,
      inner_timeBochnerPair hζV hcζV hU,
      inner_timeBochnerPair hζ.continuous hc hF]
    linarith only [hs]
  have hp := inner_eq_of_spectral_relation b μ hB hAx
  dsimp [B, W] at hp
  rw [inner_sub_right, inner_add_right, inner_sub_right, inner_add_right,
    real_inner_smul_right, real_inner_smul_right,
    inner_timeBochnerPair hddζ.continuous hc.deriv.deriv hU,
    inner_timeBochnerPair hdζ.continuous hc.deriv hU,
    inner_timeBochnerPair hζ.continuous hc hU,
    inner_timeBochnerPair hζV hcζV hU,
    inner_timeBochnerPair hζ.continuous hc hF,
    inner_timeBochnerPair hζ.continuous hc hU] at hp
  linarith only [hp]

end Yamabe3.Analysis.Delaunay
