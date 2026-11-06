import Yamabe3.Analysis.DelaunayPeriodMass

/-!
# Actual small-neck period and mass data on one smooth family

The same jointly smooth family previously constructed by a complete smooth
flow is identified with its actual clock orbit. This produces true period
mass tending to two and true periods tending to infinity. The statements
retain the same function V and do not assume any uniform bound on a
noncanonical choice of constants.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

/-- The actual angular mass tends to two when parameterized by the true
neck eta, rather than its square. -/
theorem tendsto_neck_oval_mass_zero :
    Tendsto (fun η : ℝ => ∫ θ in Icc 0 Real.pi,
      ovalMassDensity (η ^ 2) (upperSquared (η ^ 2)) θ) (𝓝[>] 0) (𝓝 2) := by
  have hsq : Tendsto (fun η : ℝ => η ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc : Continuous (fun η : ℝ => η ^ 2) := by fun_prop
      have ht := hc.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
      simpa only [zero_pow (by decide : 2 ≠ 0)] using ht
    · filter_upwards [self_mem_nhdsWithin] with η hη
      change (0 : ℝ) < η ^ 2
      exact sq_pos_of_pos (mem_Ioi.mp hη)
  exact tendsto_integral_ovalMassDensity_zero.comp hsq

/-- Uniform eventual form of the actual period/mass bounds. The same
neck-normalized v is used in both conclusions. The initial data and true
ODE are exactly those of the already constructed smooth family. -/
theorem eventually_small_neck_period_mass {ε L : ℝ} (hε : 0 < ε) :
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      0 < η ∧ 3 * η ^ 4 < 1 ∧
      ∀ v : ℝ → ℝ, ContDiff ℝ ∞ v → v 0 = η → deriv v 0 = 0 →
        (∀ t, deriv (deriv v) t = radialForce (v t)) →
        (∀ t, η ≤ v t ∧ |deriv v t| ≤ v t / 2) →
        ∃ T : ℝ, 0 < T ∧ Function.Periodic v T ∧ L < T ∧
          (∫ t in (0 : ℝ)..T, v t ^ 4) < 2 + ε := by
  have hmass : ∀ᶠ η : ℝ in 𝓝[>] 0,
      (∫ θ in Icc 0 Real.pi, ovalMassDensity (η ^ 2) (upperSquared (η ^ 2)) θ) < 2 + ε :=
    tendsto_neck_oval_mass_zero.eventually (eventually_lt_nhds (by linarith : (2 : ℝ) < 2 + ε))
  have hlog : ∀ᶠ η : ℝ in 𝓝[>] 0, Real.log η < Real.log (1 / 2 : ℝ) - L / 2 :=
    Real.tendsto_log_nhdsGT_zero.eventually (eventually_lt_atBot _)
  have hsmall : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η ∧ η < 1 / 2 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds]
      with η hη hlt
    exact ⟨hη, hlt⟩
  filter_upwards [hmass, hlog, hsmall] with η hm hl hη
  have hsq : η ^ 2 < 1 / 4 := by nlinarith [hη.1, hη.2]
  have hfour : η ^ 4 < 1 / 16 := by
    nlinarith [mul_pos (sub_pos.mpr hsq) (show (0 : ℝ) < 1 / 4 + η ^ 2 by positivity)]
  have hs : 3 * η ^ 4 < 1 := by linarith
  refine ⟨hη.1, hs, ?_⟩
  intro v hv h0 hd0 hode hb
  obtain ⟨T, hT, hp, hM, τ, hτ0, hτT, hτv⟩ :=
    exists_neck_period_with_oval_mass hη.1 hs hv h0 hd0 hode
  have hb0 : (1 / 2 : ℝ) ≤ upperSquared (η ^ 2) := by
    have hroot : (3 / 2 : ℝ) ≤ Real.sqrt (4 - 3 * (η ^ 2) ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith only [hfour])
    unfold upperSquared
    nlinarith
  have hβ : (1 / 2 : ℝ) ≤ Real.sqrt (upperSquared (η ^ 2)) :=
    Real.le_sqrt_of_sq_le (by linarith)
  have hτlower := time_lower_bound_of_logarithmic_speed (hv.differentiable (by simp))
    (fun t => hη.1.trans_le (hb t).1) (fun t => (hb t).2) hη.1
    (by norm_num : (0 : ℝ) < 1 / 2) h0 hτ0.le (by rw [hτv]; exact hβ)
  have hLτ : L < τ := by
    rw [Real.log_div (by norm_num : (1 / 2 : ℝ) ≠ 0) hη.1.ne'] at hτlower
    linarith
  exact ⟨T, hT, hp, hLτ.trans hτT, by rw [hM]; exact hm⟩

/-- A single genuine jointly smooth Delaunay family enjoys the actual
small-neck period-mass control. There is no periodic orbit, inverse, mass
estimate, or period-growth assumption in this existence theorem. -/
theorem exists_smooth_delaunay_family_with_small_neck_mass :
    ∃ V : ℝ → ℝ → ℝ,
      ContDiff ℝ ∞ (fun z : ℝ × ℝ => V z.1 z.2) ∧
      (∀ η : ℝ, 0 < η → 3 * η ^ 4 < 1 →
        V η 0 = η ∧ deriv (V η) 0 = 0 ∧
        (∀ t, η ≤ V η t ∧ V η t < 1 ∧ |deriv (V η) t| < V η t / 2) ∧
        (∀ t, deriv (deriv (V η)) t = radialForce (V η t))) ∧
      ∀ ε : ℝ, 0 < ε → ∀ L : ℝ,
        ∀ᶠ η : ℝ in 𝓝[>] 0,
          ∃ T : ℝ, 0 < T ∧ Function.Periodic (V η) T ∧ L < T ∧
            (∫ t in (0 : ℝ)..T, V η t ^ 4) < 2 + ε := by
  obtain ⟨V, hVs, hV⟩ := exists_jointly_smooth_delaunay_neck_family
  have hdata (η : ℝ) (hη : 0 < η) (hs : 3 * η ^ 4 < 1) := hV η hη hs
  refine ⟨V, hVs, ?_, ?_⟩
  · intro η hη hs
    obtain ⟨_, _, _, h0, hd0, hb, hode, _, _⟩ := hdata η hη hs
    exact ⟨h0, hd0, hb, hode⟩
  · intro ε hε L
    filter_upwards [eventually_small_neck_period_mass (L := L) hε] with η hη
    obtain ⟨_, _, _, h0, hd0, hb, hode, _, _⟩ := hdata η hη.1 hη.2.1
    have hs : ContDiff ℝ ∞ (V η) := hVs.comp (contDiff_const.prodMk contDiff_id)
    exact hη.2.2 (V η) hs h0 hd0 hode (fun t => ⟨(hb t).1, (hb t).2.2.le⟩)

end Yamabe3.Analysis.Delaunay
