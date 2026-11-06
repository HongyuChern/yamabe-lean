import Yamabe3.Analysis.DelaunayJacobi
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The actual periodic orbit normalized at its neck

The constructed orbit is translated to an attained minimum. Its derivative
there vanishes by the genuine differentiable extremum theorem. This supplies
the exact initial data (eta,0) for comparison with the smooth complete flow.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

theorem exists_delaunay_neck_solution {η : ℝ} (hη : 0 < η) (hsmall : 3 * η ^ 4 < 1) :
    ∃ (v : ℝ → ℝ) (T : ℝ),
      0 < T ∧ ContDiff ℝ ∞ v ∧ Function.Periodic v T ∧
      v 0 = η ∧ deriv v 0 = 0 ∧
      (∀ t, η ≤ v t ∧ v t < 1 ∧ |deriv v t| < v t / 2) ∧
      (∀ t, deriv (deriv v) t = radialForce (v t)) ∧
      (∀ t, 4 * deriv v t ^ 2 + v t ^ 6 - v t ^ 2 = η ^ 6 - η ^ 2) ∧
      (∀ S, 0 < S → Function.Periodic v S → T ≤ S) := by
  obtain ⟨v, T, hT, hv, hp, hb, _, _, hmin, hode, he, hpos, _, hleast⟩ :=
    exists_delaunay_periodic hη hsmall
  obtain ⟨τ, _, _, hτ⟩ := hmin
  have hlocal : IsLocalMin v τ := by
    show ∀ᶠ t in 𝓝 τ, v τ ≤ v t
    exact Eventually.of_forall fun t => by rw [hτ]; exact (hb t).1
  have hdτ : deriv v τ = 0 := hlocal.deriv_eq_zero
  let w : ℝ → ℝ := fun t => v (t + τ)
  have hw : ContDiff ℝ ∞ w := hv.comp (contDiff_id.add contDiff_const)
  have hd (t : ℝ) : HasDerivAt w (deriv v (t + τ)) t := by
    have h := ((hv.differentiable (by simp) (t + τ)).hasDerivAt).comp t
      ((hasDerivAt_id t).add_const τ)
    simpa only [Function.comp_def, id_eq, mul_one] using h
  have hdw : deriv w = fun t => deriv v (t + τ) := funext fun t => (hd t).deriv
  have hdv : ContDiff ℝ ∞ (deriv v) := (contDiff_infty_iff_deriv.mp hv).2
  have hwODE (t : ℝ) : deriv (deriv w) t = radialForce (w t) := by
    have h := ((hdv.differentiable (by simp) (t + τ)).hasDerivAt).comp t
      ((hasDerivAt_id t).add_const τ)
    simp only [Function.comp_def, id_eq, mul_one] at h
    rw [hdw, h.deriv]
    exact hode (t + τ)
  refine ⟨w, T, hT, hw, ?_, ?_, ?_, ?_, hwODE, ?_, ?_⟩
  · intro t
    change v ((t + T) + τ) = v (t + τ)
    rw [show (t + T) + τ = (t + τ) + T by ring]
    exact hp (t + τ)
  · simpa only [w, zero_add] using hτ
  · rw [hdw]
    simpa only [zero_add] using hdτ
  · intro t
    rw [hdw]
    exact ⟨(hb (t + τ)).1, (hpos (t + τ)).2.1, (hpos (t + τ)).2.2⟩
  · intro t
    rw [hdw]
    exact he (t + τ)
  · intro S hS hperiod
    apply hleast S hS
    intro t
    have h := hperiod (t - τ)
    change v ((t - τ + S) + τ) = v ((t - τ) + τ) at h
    simpa only [show (t - τ + S) + τ = t + S by ring, sub_add_cancel] using h

#print axioms exists_delaunay_neck_solution

end Yamabe3.Analysis.Delaunay
