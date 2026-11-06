import Yamabe3.Analysis.UniformElliptic.UniformPrincipalHessian

/-!
# One numerical Hessian estimate for an actual rescaled coefficient family

Continuity and the actual identity value at the origin produce one radius
before the scale and the test function are quantified. The rescaled arrays
then satisfy the proved perturbative estimate with the numerical constant 4.
This supplies a genuine uniform coefficient-family statement, rather than
reusing constants chosen separately for each member of the family.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set MeasureTheory Filter Metric
open scoped ContDiff Topology

namespace Yamabe3.Analysis.UniformElliptic

local notation "E" => EuclideanSpace ℝ (Fin 3)

/-- The actual continuous coefficient field has a common entrywise
identity neighborhood in all nine entries. -/
theorem exists_coefficient_identity_radius
    {a : E → Matrix (Fin 3) (Fin 3) ℝ}
    (ha : ∀ i j, ContinuousAt (fun x => a x i j) 0) (hzero : a 0 = 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : E, ‖x‖ < ρ → ∀ i j : Fin 3,
      |a x i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 / 6 := by
  have hevent : ∀ᶠ x in 𝓝 (0 : E), ∀ i j : Fin 3,
      |a x i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < 1 / 6 := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    have h := (ha i j).tendsto.eventually
      (Metric.ball_mem_nhds (a 0 i j) (by norm_num : (0 : ℝ) < 1 / 6))
    simpa only [mem_ball, Real.dist_eq, hzero] using h
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨ρ, hρ, ?_⟩
  intro x hx i j
  exact (hball (by simpa using hx) i j).le

/-- A fixed spatial test ball and an actual continuous identity-normalized
coefficient field give one radius and the same numerical Hessian estimate
for all smaller rescalings and all smooth compactly supported tests. -/
theorem exists_uniform_rescaled_hessian_energy
    {a : E → Matrix (Fin 3) (Fin 3) ℝ}
    (ha : ∀ i j, Continuous (fun x => a x i j)) (hzero : a 0 = 1)
    {R : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 ≤ r → r < δ →
      ∀ u : E → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u → tsupport u ⊆ ball 0 R →
        (∫ x, hessianSq u x) ≤
          4 * (∫ x, principalPart (fun y => a (r • y)) u x ^ 2) := by
  obtain ⟨ρ, hρ, hρbound⟩ := exists_coefficient_identity_radius
    (fun i j => (ha i j).continuousAt) hzero
  refine ⟨ρ / R, div_pos hρ hR, ?_⟩
  intro r hr hrδ u hu hc hs
  have har : ∀ i j : Fin 3, Continuous (fun y : E => a (r • y) i j) := by
    intro i j
    exact (ha i j).comp (continuous_const_smul r)
  apply principal_hessian_energy_le_four_three (a := fun y => a (r • y)) (u := u) har hu hc
  intro x hx i j
  apply hρbound
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  have hxR : ‖x‖ < R := by simpa using hs hx
  have hrR : r * R < ρ := (lt_div_iff₀ hR).mp hrδ
  exact (mul_le_mul_of_nonneg_left hxR.le hr).trans_lt hrR

#print axioms exists_coefficient_identity_radius
#print axioms exists_uniform_rescaled_hessian_energy

end Yamabe3.Analysis.UniformElliptic
