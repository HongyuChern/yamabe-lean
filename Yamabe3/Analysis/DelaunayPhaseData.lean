import Yamabe3.Analysis.NativeDelaunayHalfEndPotential
import Mathlib.Analysis.Calculus.MeanValue

/-! Original orbit data, with no solver or regularity estimate as a field.
The derivative bound is derived from the original positive energy parameter.
No smaller threshold is introduced. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff Topology BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem actual_orbit_energy_constant (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v)
    (hODE : ∀ t, deriv (deriv v) t = radialForce (v t)) (t : ℝ) :
    4 * deriv v t ^ 2 + v t ^ 6 - v t ^ 2 =
      4 * deriv v 0 ^ 2 + v 0 ^ 6 - v 0 ^ 2 := by
  have h₀ : Differentiable ℝ v := hv.differentiable (by simp)
  have h₁ : Differentiable ℝ (deriv v) :=
    (contDiff_infty_iff_deriv.mp hv).2.differentiable (by simp)
  let H (x : ℝ) := 4 * deriv v x ^ 2 + v x ^ 6 - v x ^ 2
  have hd (x : ℝ) : HasDerivAt H 0 x := by
    have hh := (((h₁ x).hasDerivAt.pow 2).const_mul 4).add
      ((h₀ x).hasDerivAt.pow 6) |>.sub ((h₀ x).hasDerivAt.pow 2)
    convert hh using 1 <;> first | rfl | (rw [hODE, radialForce]; ring)
  exact is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
    (fun x => (hd x).deriv) t 0

theorem actual_orbit_derivative_bound (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v)
    (hODE : ∀ t, deriv (deriv v) t = radialForce (v t))
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {q : ℝ} (hq : 0 ≤ q)
    (hE : q = v 0 ^ 2 - v 0 ^ 6 - 4 * deriv v 0 ^ 2) :
    ∀ t, |deriv v t| ≤ 1/2 := by
  intro t
  have he := actual_orbit_energy_constant v hv hODE t
  have hv2 : v t ^ 2 ≤ 1 := pow_le_one₀ (hb t).1 (hb t).2
  have hv6 : 0 ≤ v t ^ 6 := by positivity
  have hs : deriv v t ^ 2 ≤ (1/2:ℝ)^2 := by nlinarith
  exact (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/2)).mp (by simpa only [sq_abs] using hs)

/-- Only the actual ODE orbit and the original integrated gap. -/
structure DelaunayPhaseData (κ : ℝ) where
  orbit : ℝ → ℝ
  smooth : ContDiff ℝ ∞ orbit
  bounded : ∀ t, 0 ≤ orbit t ∧ orbit t ≤ 1
  derivative_bound : ∀ t, |deriv orbit t| ≤ 1/2
  ode : ∀ t, deriv (deriv orbit) t = radialForce (orbit t)
  phase : ℝ
  kernel_bound : ∀ t, (∫ s : ℝ, spectralMajorant (5/2) (-2) s *
    |delaunayPhasePotentialBCF orbit smooth.continuous bounded phase (t-s)|) ≤ κ

def DelaunayPhaseData.potential {κ : ℝ} (p : DelaunayPhaseData κ) : ℝ →ᵇ ℝ :=
  delaunayPhasePotentialBCF p.orbit p.smooth.continuous p.bounded p.phase

theorem DelaunayPhaseData.potential_smooth {κ : ℝ} (p : DelaunayPhaseData κ) :
    ContDiff ℝ ∞ (fun t : ℝ => p.potential t) := by
  change ContDiff ℝ ∞ (fun t : ℝ => (15/4)*p.orbit (t+p.phase)^4)
  have hs := p.smooth
  fun_prop

theorem DelaunayPhaseData.potential_nonneg {κ : ℝ} (p : DelaunayPhaseData κ) :
    ∀ t, 0 ≤ p.potential t := delaunayPhasePotentialBCF_nonneg _ _ _ _

theorem exists_uniform_small_energy_phase_data :
    ∃ (κ q₀ : ℝ), 0 ≤ κ ∧ κ < 1 ∧ 0 < q₀ ∧
      ∀ (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v),
        (∀ t, deriv (deriv v) t = radialForce (v t)) → 0 < v 0 →
        ∀ q : ℝ, 0 < q → q < q₀ →
          q = v 0 ^ 2 - v 0 ^ 6 - 4 * deriv v 0 ^ 2 →
          ∀ τ : ℝ, ∃ p : DelaunayPhaseData κ, p.orbit = v ∧ p.phase = τ := by
  obtain ⟨κ,q₀,hκ0,hκ1,hq₀,hp⟩ := exists_uniform_small_energy_halfEnd_phase_potential
  refine ⟨κ,q₀,hκ0,hκ1,hq₀,?_⟩
  intro v hv hODE hv0 q hq hqq hE τ
  obtain ⟨hb,hpot⟩ := hp v hv hODE hv0 q hq hqq hE
  exact ⟨⟨v,hv,hb,actual_orbit_derivative_bound v hv hODE hb hq.le hE,
    hODE,τ,(hpot τ).2.2.2⟩,rfl,rfl⟩

#print axioms actual_orbit_energy_constant
#print axioms actual_orbit_derivative_bound
#print axioms exists_uniform_small_energy_phase_data
end Yamabe3.Analysis.Delaunay
