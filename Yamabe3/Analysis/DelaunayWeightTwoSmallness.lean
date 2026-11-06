import Yamabe3.Analysis.DelaunaySmallNeckMass
import Yamabe3.Analysis.DelaunayKernelPeriodBound

/-!
# Actual small-neck contraction at the common decay weight two

A fixed strictly positive threshold gap, the true time mass tending to two,
and the true period tending to infinity produce one contraction factor
strictly below one for all sufficiently small necks. Every convolution
center and every phase translate is covered. The estimate applies to the
same actual normalized ODE orbit, not to independently chosen period data.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

/-- One neck-independent contraction constant for the actual weight -2
high-mode potential kernel, uniformly in time and phase. -/
theorem exists_uniform_small_neck_weightTwo_bound :
    ∃ κ : ℝ, 0 ≤ κ ∧ κ < 1 ∧
      ∀ᶠ η : ℝ in 𝓝[>] 0,
        0 < η ∧ 3 * η ^ 4 < 1 ∧
        ∀ v : ℝ → ℝ, ContDiff ℝ ∞ v → v 0 = η → deriv v 0 = 0 →
          (∀ t, deriv (deriv v) t = radialForce (v t)) →
          (∀ t, η ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ v t / 2) →
          ∀ τ t : ℝ,
            (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s *
              ((15 / 4) * v (t - s + τ) ^ 4)) ≤ κ := by
  let B : ℝ := (5 / 3) * (1 - weightTwoThreshold)
  let g : ℝ := 1 - B
  have hThreshold0 : 0 < weightTwoThreshold := Real.exp_pos _
  have hThreshold1 : weightTwoThreshold ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hB0 : 0 ≤ B := by
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr hThreshold1)
  have hB1 : B < 1 := weightTwo_threshold_gap
  have hg : 0 < g := sub_pos.mpr hB1
  let κ : ℝ := (1 + B) / 2
  have hκ0 : 0 ≤ κ := by dsimp [κ]; linarith
  have hκ1 : κ < 1 := by dsimp [κ]; linarith
  have hlim : Tendsto (fun T : ℝ => (5 / 3 : ℝ) * Real.exp (-T / 4)) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-(1 / 4 : ℝ)) < 0))).const_mul (5 / 3 : ℝ)
    convert h using 1 <;> try norm_num
    funext T
    congr 2
    ring
  have htail : ∀ᶠ T : ℝ in atTop, (5 / 3 : ℝ) * Real.exp (-T / 4) < g / 6 :=
    hlim.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < g / 6))
  obtain ⟨L, hL⟩ := eventually_atTop.mp htail
  refine ⟨κ, hκ0, hκ1, ?_⟩
  filter_upwards [eventually_small_neck_period_mass (ε := g / 6) (L := L) (by linarith)] with η hη
  refine ⟨hη.1, hη.2.1, ?_⟩
  intro v hv h0 hd0 hode hb τ t
  obtain ⟨T, hT, hp, hLT, hM⟩ := hη.2.2 v hv h0 hd0 hode
    (fun s => ⟨(hb s).1, (hb s).2.2⟩)
  have hvb (s : ℝ) : 0 ≤ v s ∧ v s ≤ 1 :=
    ⟨(hη.1.trans_le (hb s).1).le, (hb s).2.1⟩
  have hbound := weightTwo_periodic_potential_bound hv.continuous hvb hT.le hp (t + τ)
  have hterm : (3 / 4) * weightTwoThreshold * ((∫ s in (0 : ℝ)..T, v s ^ 4) - 2) ≤ g / 8 := by
    have hmass : (∫ s in (0 : ℝ)..T, v s ^ 4) - 2 ≤ g / 6 := by linarith
    have h1 := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ (3 / 4 : ℝ) * weightTwoThreshold)
    have h2 := mul_le_mul_of_nonneg_right hThreshold1 (show 0 ≤ g / 8 by linarith)
    nlinarith only [h1, h2]
  have hTtail := hL T hLT.le
  have hfinal : (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s *
      ((15 / 4) * v ((t + τ) - s) ^ 4)) ≤ κ := by
    have hgap0 : 0 < 1 - (5 / 3) * (1 - weightTwoThreshold) := hg
    dsimp only [B, g, κ] at hbound hterm hTtail ⊢
    nlinarith only [hbound, hterm, hTtail, hgap0]
  convert hfinal using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun s => by
    dsimp only
    rw [show t - s + τ = t + τ - s by ring]

end Yamabe3.Analysis.Delaunay
