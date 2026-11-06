import Yamabe3.Analysis.ExponentialKernelInverse
import Yamabe3.Analysis.DelaunayEnergy
import Yamabe3.Analysis.DelaunayJacobi
import Mathlib.Topology.MetricSpace.Contracting

/-!
# An actual parameter-uniform scalar high-mode inverse

The constant-mass kernel and Banach contraction on bounded continuous
functions construct the solution. Its true differential equation then
bootstraps smoothness. For numerical angular eigenvalue at least six the
bound is independent of the neck parameter. The native sphere spectrum
and reconstruction of an angular series remain separate obligations.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

def potentialIteration (k : ℝ) (hk : 0 < k) (V F : ℝ →ᵇ ℝ)
    (u : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ := massResolvent k hk (F - V * u)

theorem potentialIteration_contracting {k : ℝ} (hk : 0 < k)
    (V F : ℝ →ᵇ ℝ) (hV : ‖V‖ < k ^ 2) :
    ContractingWith ⟨‖V‖ / k ^ 2, by positivity⟩ (potentialIteration k hk V F) := by
  refine ⟨?_, ?_⟩
  · change ‖V‖ / k ^ 2 < 1
    exact (div_lt_one (sq_pos_of_pos hk)).mpr hV
  · apply LipschitzWith.of_dist_le_mul
    intro u w
    change dist (massResolvent k hk (F - V * u)) (massResolvent k hk (F - V * w)) ≤
      (‖V‖ / k ^ 2) * dist u w
    have hsource : dist (F - V * u) (F - V * w) ≤ ‖V‖ * dist u w := by
      rw [dist_eq_norm, dist_eq_norm]
      have heq : (F - V * u) - (F - V * w) = -(V * (u - w)) := by ring
      rw [heq, norm_neg]
      exact norm_mul_le _ _
    calc
      _ ≤ dist (F - V * u) (F - V * w) / k ^ 2 := massResolvent_dist_le hk _ _
      _ ≤ (‖V‖ * dist u w) / k ^ 2 :=
        div_le_div_of_nonneg_right hsource (sq_nonneg _)
      _ = _ := by ring

/-- The actual contraction fixed point in the complete bounded-continuous
function space. There is no invertibility assumption in this definition. -/
def smallPotentialInverse (k : ℝ) (hk : 0 < k) (V : ℝ →ᵇ ℝ)
    (hV : ‖V‖ < k ^ 2) (F : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  (potentialIteration_contracting hk V F hV).fixedPoint (potentialIteration k hk V F)

theorem smallPotentialInverse_fixed {k : ℝ} (hk : 0 < k) (V : ℝ →ᵇ ℝ)
    (hV : ‖V‖ < k ^ 2) (F : ℝ →ᵇ ℝ) :
    massResolvent k hk (F - V * smallPotentialInverse k hk V hV F) =
      smallPotentialInverse k hk V hV F :=
  (potentialIteration_contracting hk V F hV).fixedPoint_isFixedPt

theorem smallPotentialInverse_differentiable_equation {k : ℝ} (hk : 0 < k)
    (V : ℝ →ᵇ ℝ) (hV : ‖V‖ < k ^ 2) (F : ℝ →ᵇ ℝ) :
    let u := smallPotentialInverse k hk V hV F
    Differentiable ℝ (fun t => u t) ∧
      Differentiable ℝ (deriv (fun t => u t)) ∧
      ∀ t, deriv (deriv (fun t => u t)) t = k ^ 2 * u t + F t - V t * u t := by
  dsimp only
  let u := smallPotentialInverse k hk V hV F
  have hrep : massInverse k ((F - V * u : ℝ →ᵇ ℝ) : ℝ → ℝ) = (fun t => u t) := by
    funext t
    exact congrArg (fun H : ℝ →ᵇ ℝ => H t) (smallPotentialInverse_fixed hk V hV F)
  have h := massInverse_differentiable_equation hk (F - V * u).continuous
    (fun t => by simpa only [Real.norm_eq_abs] using (F - V * u).norm_coe_le_norm t)
  rw [hrep] at h
  refine ⟨h.1, h.2.1, fun t => ?_⟩
  have he := h.2.2 t
  change deriv (deriv (fun t => u t)) t = k ^ 2 * u t + (F t - V t * u t) at he
  simpa only [add_sub_assoc] using he

theorem smallPotentialInverse_norm_bound {k : ℝ} (hk : 0 < k)
    (V : ℝ →ᵇ ℝ) (hV : ‖V‖ < k ^ 2) (F : ℝ →ᵇ ℝ) :
    ‖smallPotentialInverse k hk V hV F‖ ≤ ‖F‖ / (k ^ 2 - ‖V‖) := by
  let u := smallPotentialInverse k hk V hV F
  have heq := smallPotentialInverse_fixed hk V hV F
  have hn : ‖u‖ ≤ (‖F‖ + ‖V‖ * ‖u‖) / k ^ 2 := by
    calc
      ‖u‖ = ‖massResolvent k hk (F - V * u)‖ := congrArg norm heq.symm
      _ ≤ ‖F - V * u‖ / k ^ 2 := massResolvent_norm_le hk _
      _ ≤ (‖F‖ + ‖V‖ * ‖u‖) / k ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_mul_le V u))
  have hmul := (le_div_iff₀ (sq_pos_of_pos hk)).mp hn
  apply (le_div_iff₀ (sub_pos.mpr hV)).mpr
  dsimp only [u] at hmul ⊢
  nlinarith

/-- Smoothness is derived from the actual second-order equation, starting
only with the differentiability furnished by the integral kernel. -/
theorem contDiff_of_second_order_linear {u V F : ℝ → ℝ} {a : ℝ}
    (hu : Differentiable ℝ u) (hdu : Differentiable ℝ (deriv u))
    (hV : ContDiff ℝ ∞ V) (hF : ContDiff ℝ ∞ F)
    (heq : ∀ t, deriv (deriv u) t = a * u t + F t - V t * u t) :
    ContDiff ℝ ∞ u := by
  have hn : ∀ n : ℕ, ContDiff ℝ n u ∧ ContDiff ℝ n (deriv u) := by
    intro n
    induction n with
    | zero => exact ⟨contDiff_zero.mpr hu.continuous, contDiff_zero.mpr hdu.continuous⟩
    | succ n ih =>
      have hD2 : ContDiff ℝ n (deriv (deriv u)) := by
        have hf : deriv (deriv u) = fun t => a * u t + F t - V t * u t := funext heq
        rw [hf]
        exact ((contDiff_const.mul ih.1).add (contDiff_infty.mp hF n)).sub
          ((contDiff_infty.mp hV n).mul ih.1)
      constructor
      · exact contDiff_succ_iff_deriv.mpr ⟨hu, by simp, ih.2⟩
      · exact contDiff_succ_iff_deriv.mpr ⟨hdu, by simp, hD2⟩
  exact contDiff_infty.mpr fun n => (hn n).1

theorem smallPotentialInverse_contDiff {k : ℝ} (hk : 0 < k)
    (V : ℝ →ᵇ ℝ) (hV : ‖V‖ < k ^ 2) (F : ℝ →ᵇ ℝ)
    (hVs : ContDiff ℝ ∞ (fun t => V t)) (hFs : ContDiff ℝ ∞ (fun t => F t)) :
    ContDiff ℝ ∞ (fun t => smallPotentialInverse k hk V hV F t) := by
  have h := smallPotentialInverse_differentiable_equation hk V hV F
  exact contDiff_of_second_order_linear h.1 h.2.1 hVs hFs h.2.2

/-- Every bounded smooth source in a numerical high angular mode has an
actual smooth bounded solution. The constant is independent of the neck. -/
theorem exists_bounded_high_mode_solution {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvbound : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {eigenvalue : ℝ} (heigen : 6 ≤ eigenvalue)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {A : ℝ} (hA : 0 ≤ A)
    (hFbound : ∀ t, |F t| ≤ A) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧
      (∀ t, modelJacobi v eigenvalue u t = F t) ∧
      (∀ t, |u t| ≤ A / (eigenvalue - 7 / 2)) := by
  let k : ℝ := Real.sqrt (eigenvalue + 1 / 4)
  have hk : 0 < k := Real.sqrt_pos.mpr (by linarith)
  have hk2 : k ^ 2 = eigenvalue + 1 / 4 := Real.sq_sqrt (by linarith)
  let Vfun : ℝ → ℝ := fun t => (15 / 4) * v t ^ 4
  have hVs : ContDiff ℝ ∞ Vfun := contDiff_const.mul (hv.pow 4)
  have hVbound (t : ℝ) : ‖Vfun t‖ ≤ 15 / 4 := by
    have hp : v t ^ 4 ≤ 1 := pow_le_one₀ (hvbound t).1 (hvbound t).2
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [Vfun]; positivity)]
    dsimp [Vfun]
    linarith
  let V : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    Vfun hVs.continuous (15 / 4) hVbound
  have hVnorm : ‖V‖ ≤ 15 / 4 :=
    (BoundedContinuousFunction.norm_le (by norm_num)).mpr hVbound
  have hVk : ‖V‖ < k ^ 2 := by rw [hk2]; linarith
  let Fb : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup F hF.continuous A
    (fun t => by simpa only [Real.norm_eq_abs] using hFbound t)
  have hFnorm : ‖Fb‖ ≤ A := by
    apply (BoundedContinuousFunction.norm_le hA).mpr
    intro t
    change ‖F t‖ ≤ A
    simpa only [Real.norm_eq_abs] using hFbound t
  let u := smallPotentialInverse k hk V hVk Fb
  have hdiff := smallPotentialInverse_differentiable_equation hk V hVk Fb
  refine ⟨fun t => u t, smallPotentialInverse_contDiff hk V hVk Fb hVs hF, ?_, ?_⟩
  · intro t
    have he := hdiff.2.2 t
    change deriv (deriv (fun t => u t)) t = k ^ 2 * u t + F t - (15 / 4) * v t ^ 4 * u t at he
    unfold modelJacobi
    rw [he, hk2]
    ring
  · intro t
    have hden : 0 < eigenvalue - 7 / 2 := by linarith
    calc
      |u t| ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using u.norm_coe_le_norm t
      _ ≤ ‖Fb‖ / (k ^ 2 - ‖V‖) := smallPotentialInverse_norm_bound hk V hVk Fb
      _ ≤ ‖Fb‖ / (eigenvalue - 7 / 2) := by
        apply div_le_div_of_nonneg_left (norm_nonneg _) hden
        rw [hk2]
        linarith
      _ ≤ A / (eigenvalue - 7 / 2) := div_le_div_of_nonneg_right hFnorm hden.le

/-- The periodic background and all numerical scalar high-mode solution
operators are obtained from the energy parameters, with no supplied inverse. -/
theorem exists_delaunay_uniform_high_mode_inverse {ε e : ℝ}
    (hε : 0 < ε) (he : 0 < e) (hsmall : ε ^ 2 * e < 3 / 8) :
    ∃ (v : ℝ → ℝ) (T : ℝ),
      0 < T ∧ ContDiff ℝ ∞ v ∧ Function.Periodic v T ∧
      (∀ t, ε * Real.sqrt e ≤ v t ∧ v t < 1) ∧
      (∀ t, deriv (deriv v) t = radialForce (v t)) ∧
      ∀ (eigenvalue : ℝ), 6 ≤ eigenvalue → ∀ (F : ℝ → ℝ) (A : ℝ),
        ContDiff ℝ ∞ F → 0 ≤ A → (∀ t, |F t| ≤ A) →
        ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧
          (∀ t, modelJacobi v eigenvalue u t = F t) ∧
          (∀ t, |u t| ≤ A / (eigenvalue - 7 / 2)) := by
  obtain ⟨η, v, T, hη, _, hηlow, _, hT, hs, hp, hb, _, _, _, hode, _, _, _⟩ :=
    exists_delaunay_energy_parameters hε he hsmall
  refine ⟨v, T, hT, hs, hp, fun t => ⟨hηlow.trans (hb t).1, (hb t).2⟩, hode, ?_⟩
  intro eigenvalue heigen F A hF hA hFb
  exact exists_bounded_high_mode_solution hs
    (fun t => ⟨hη.le.trans (hb t).1, (hb t).2.le⟩) heigen hF hA hFb

#print axioms smallPotentialInverse_differentiable_equation
#print axioms smallPotentialInverse_norm_bound
#print axioms exists_delaunay_uniform_high_mode_inverse

end Yamabe3.Analysis.Delaunay
