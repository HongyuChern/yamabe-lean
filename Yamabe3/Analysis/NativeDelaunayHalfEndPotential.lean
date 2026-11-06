import Yamabe3.Analysis.DelaunayCauchyKernel
import Yamabe3.Analysis.NativeCommonInverseCLM

/-!
# Actual small-energy Delaunay potentials for every half-end phase

The existing same-orbit Cauchy theorem chooses one strict integrated
potential gap before the orbit and phase. The potential below is the
literal translate `(15/4) * v(t + τ)^4` of that same orbit, represented
by the already constructed bounded continuous potential. Its pointwise,
bounded-function norm and integrated bounds are proved for every phase.

No whole-line bounded-function continuity in an orbit parameter is
asserted. The phase argument uses only translation of the convolution
center. This supplies actual legal inputs to the high half-end solver;
it does not assert a coupled exterior solution.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

/-- The same actual Delaunay potential translated by the chosen phase. -/
def delaunayPhasePotentialBCF (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (τ : ℝ) : ℝ →ᵇ ℝ :=
  delaunayPotentialBCF (fun t => v (t + τ))
    (hv.comp (continuous_id.add continuous_const)) (fun t => hb (t + τ))

@[simp] theorem delaunayPhasePotentialBCF_apply (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (τ t : ℝ) :
    delaunayPhasePotentialBCF v hv hb τ t = (15 / 4) * v (t + τ) ^ 4 := rfl

theorem delaunayPhasePotentialBCF_nonneg (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (τ t : ℝ) :
    0 ≤ delaunayPhasePotentialBCF v hv hb τ t := by
  rw [delaunayPhasePotentialBCF_apply]
  positivity

theorem delaunayPhasePotentialBCF_le (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (τ t : ℝ) :
    delaunayPhasePotentialBCF v hv hb τ t ≤ 15 / 4 := by
  rw [delaunayPhasePotentialBCF_apply]
  have hpow : v (t + τ) ^ 4 ≤ 1 := pow_le_one₀ (hb (t + τ)).1 (hb (t + τ)).2
  linarith only [hpow]

theorem delaunayPhasePotentialBCF_norm_le (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (τ : ℝ) :
    ‖delaunayPhasePotentialBCF v hv hb τ‖ ≤ 15 / 4 := by
  apply (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 15 / 4)).mpr
  intro t
  rw [Real.norm_of_nonneg (delaunayPhasePotentialBCF_nonneg v hv hb τ t)]
  exact delaunayPhasePotentialBCF_le v hv hb τ t

/-- Translation of the actual convolution center gives the same bound
for every phase, without a claim about any parameter-space topology. -/
theorem delaunayPhasePotentialBCF_integral_bound
    (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {κ : ℝ}
    (hkernel : ∀ t : ℝ, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s *
      ((15 / 4) * v (t - s) ^ 4)) ≤ κ) (τ t : ℝ) :
    (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s *
      |delaunayPhasePotentialBCF v hv hb τ (t - s)|) ≤ κ := by
  calc
    _ = ∫ s : ℝ, spectralMajorant (5 / 2) (-2) s *
        ((15 / 4) * v ((t + τ) - s) ^ 4) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by
        dsimp only
        rw [abs_of_nonneg (delaunayPhasePotentialBCF_nonneg v hv hb τ (t - s)),
          delaunayPhasePotentialBCF_apply,
          show t - s + τ = t + τ - s by ring]
    _ ≤ κ := hkernel (t + τ)

/-- One actual energy threshold and strict kernel gap precede every
original orbit and every phase. All inputs required by the positive
high half-end construction are produced from the same smooth ODE orbit. -/
theorem exists_uniform_small_energy_halfEnd_phase_potential :
    ∃ (κ q₀ : ℝ), 0 ≤ κ ∧ κ < 1 ∧ 0 < q₀ ∧
      ∀ (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v),
        (∀ t, deriv (deriv v) t = radialForce (v t)) → 0 < v 0 →
        ∀ q : ℝ, 0 < q → q < q₀ →
          q = v 0 ^ 2 - v 0 ^ 6 - 4 * deriv v 0 ^ 2 →
          ∃ hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1,
            ∀ τ : ℝ,
              (∀ t : ℝ, 0 ≤ delaunayPhasePotentialBCF v hv.continuous hb τ t) ∧
              (∀ t : ℝ, delaunayPhasePotentialBCF v hv.continuous hb τ t ≤ 15 / 4) ∧
              ‖delaunayPhasePotentialBCF v hv.continuous hb τ‖ ≤ 15 / 4 ∧
              ∀ t : ℝ, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s *
                |delaunayPhasePotentialBCF v hv.continuous hb τ (t - s)|) ≤ κ := by
  obtain ⟨κ, q₀, hκ0, hκ1, hq₀, hproduce⟩ :=
    exists_uniform_small_energy_same_orbit_kernel_bound
  refine ⟨κ, q₀, hκ0, hκ1, hq₀, ?_⟩
  intro v hv hode hv0 q hq hqq hE
  obtain ⟨hb, hkernel⟩ := hproduce v hv hode hv0 q hq hqq hE
  refine ⟨hb, ?_⟩
  intro τ
  exact ⟨delaunayPhasePotentialBCF_nonneg v hv.continuous hb τ,
    delaunayPhasePotentialBCF_le v hv.continuous hb τ,
    delaunayPhasePotentialBCF_norm_le v hv.continuous hb τ,
    delaunayPhasePotentialBCF_integral_bound v hv.continuous hb hkernel τ⟩

#print axioms delaunayPhasePotentialBCF_integral_bound
#print axioms exists_uniform_small_energy_halfEnd_phase_potential

end Yamabe3.Analysis.Delaunay
