import Yamabe3.Analysis.DelaunayOvalMass
import Yamabe3.Analysis.DelaunaySmoothFamily
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The true time mass and length of the same Delaunay orbit

The actual positive clock integral is connected to any neck-normalized
Delaunay solution by uniqueness for the genuine polynomial phase field.
Change of variables then identifies its time mass with the angular mass,
without replacing the chosen orbit by an unrelated existential witness.
The log-derivative estimate supplies a genuine period lower bound.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

/-- Actual IVP uniqueness for the polynomial radial equation, with no
Lipschitz, inverse, or global-flow certificate supplied by the caller. -/
theorem radial_ode_eq_of_initial {v w : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w)
    (hveq : ∀ t, deriv (deriv v) t = radialForce (v t))
    (hweq : ∀ t, deriv (deriv w) t = radialForce (w t))
    (h0 : v 0 = w 0) (hd0 : deriv v 0 = deriv w 0) : v = w := by
  let F : ℝ × ℝ → ℝ × ℝ := fun x => (x.2, radialForce x.1)
  have hF : ContDiff ℝ ∞ F := by unfold F radialForce; fun_prop
  have hstate (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u)
      (heq : ∀ t, deriv (deriv u) t = radialForce (u t)) (t : ℝ) :
      HasDerivAt (fun s => (u s, deriv u s)) (F (u t, deriv u t)) t := by
    have hdu := (contDiff_infty_iff_deriv.mp hu).2
    have h1 := (hu.differentiable (by simp) t).hasDerivAt
    have h2 := (hdu.differentiable (by simp) t).hasDerivAt
    rw [heq t] at h2
    exact h1.prodMk h2
  have he : EqOn (fun t => (v t, deriv v t)) (fun t => (w t, deriv w t)) univ :=
    Poincare.ODE.eqOn_of_hasDerivAt isOpen_univ hF.contDiffOn isOpen_univ isPreconnected_univ
      (fun t _ => ⟨mem_univ _, hstate v hv hveq t⟩)
      (fun t _ => ⟨mem_univ _, hstate w hw hweq t⟩) (mem_univ (0 : ℝ))
      (Prod.ext h0 hd0)
  exact funext fun t => congrArg Prod.fst (he (mem_univ t))

/-- The actual chosen neck solution has a genuine positive period whose
true fourth-power time integral is the canceled angular integral. Its true
maximum is attained strictly inside that period. -/
theorem exists_neck_period_with_oval_mass {η : ℝ} (hη : 0 < η)
    (hsmall : 3 * η ^ 4 < 1) {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (h0 : v 0 = η) (hd0 : deriv v 0 = 0)
    (hode : ∀ t, deriv (deriv v) t = radialForce (v t)) :
    ∃ T : ℝ, 0 < T ∧ Function.Periodic v T ∧
      (∫ t in (0 : ℝ)..T, v t ^ 4) =
        ∫ θ in Icc 0 Real.pi, ovalMassDensity (η ^ 2) (upperSquared (η ^ 2)) θ ∧
      ∃ τ : ℝ, 0 < τ ∧ τ < T ∧ v τ = Real.sqrt (upperSquared (η ^ 2)) := by
  let a := η ^ 2
  let b := upperSquared a
  have ha : 0 < a := sq_pos_of_pos hη
  have has : 3 * a ^ 2 < 1 := by dsimp [a]; nlinarith only [hsmall]
  obtain ⟨hab, hb, hlevel⟩ := upperSquared_properties ha has
  have hf := ovalDensity_contDiff ha hab.le
  obtain ⟨θ, T, hTf, hT, hθ, hmono, hθ0, hθd, hright, hleft, hshift⟩ :=
    exists_smooth_periodic_clock_inverse hf Real.pi_pos (ovalDensity_periodic a b)
      (by norm_num : (0 : ℝ) < 1) (ovalDensity_ge_one ha hab.le hb.le) 0
  let w : ℝ → ℝ := fun t => ovalProfile a b (θ t)
  let z : ℝ → ℝ := fun t => ovalVelocity a b (θ t)
  have hspeed (t : ℝ) : HasDerivAt θ (ovalSpeed a b (θ t)) t := by
    simpa only [ovalDensity, inv_inv] using hθd t
  have hwd (t : ℝ) : HasDerivAt w (z t) t := by
    have h := (ovalProfile_hasDerivAt ha hab.le (θ t)).comp t (hspeed t)
    rw [ovalProfile_derivative_speed ha hab.le] at h
    exact h
  have hdw : deriv w = z := funext fun t => (hwd t).deriv
  have hweq (t : ℝ) : deriv (deriv w) t = radialForce (w t) := by
    have h := (ovalVelocity_hasDerivAt ha hab.le (θ t)).comp t (hspeed t)
    rw [ovalVelocity_derivative_speed ha hab.le hlevel] at h
    rw [hdw]
    exact h.deriv
  have hw : ContDiff ℝ ∞ w := (ovalProfile_contDiff ha hab.le).comp hθ
  have hw0 : w 0 = η := by
    simp only [w, hθ0, ovalProfile, ovalSquared, Real.sin_zero,
      zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
    exact Real.sqrt_sq hη.le
  have hdw0 : deriv w 0 = 0 := by
    rw [hdw]
    simp only [z, hθ0, ovalVelocity, Real.sin_zero, mul_zero, zero_mul]
  have heq : v = w := radial_ode_eq_of_initial hv hw hode hweq (h0.trans hw0.symm)
    (hd0.trans hdw0.symm)
  have hp : Function.Periodic v T := by
    rw [heq]
    intro t
    change ovalProfile a b (θ (t + T)) = ovalProfile a b (θ t)
    rw [hshift]
    exact ovalProfile_periodic a b (θ t)
  have hθT : θ T = Real.pi := by simpa only [zero_add, hθ0] using hshift 0
  let τ := timePrimitive (ovalDensity a b) 0 (Real.pi / 2)
  have hθτ : θ τ = Real.pi / 2 := hleft _
  have hτ0 : 0 < τ := by
    by_contra hn
    have h := hmono.monotone (le_of_not_gt hn)
    rw [hθτ, hθ0] at h
    linarith [Real.pi_pos]
  have hτT : τ < T := by
    by_contra hn
    have h := hmono.monotone (le_of_not_gt hn)
    rw [hθτ, hθT] at h
    linarith [Real.pi_pos]
  have hmax : v τ = Real.sqrt b := by
    rw [heq]
    simp only [w, hθτ, ovalProfile, ovalSquared, Real.sin_pi_div_two, one_pow, mul_one]
    congr 1
    ring
  refine ⟨T, hT, hp, ?_, τ, hτ0, hτT, hmax⟩
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := Real.pi)
    (fun x _ => timePrimitive_hasDerivAt hf.continuous 0 x)
    hf.continuous.continuousOn (hv.continuous.pow 4)
  have hstart : timePrimitive (ovalDensity a b) 0 0 = 0 := by
    simp only [timePrimitive, intervalIntegral.integral_same]
  have hend : timePrimitive (ovalDensity a b) 0 Real.pi = T := by
    simpa only [timePrimitive, zero_add] using hTf.symm
  rw [hstart, hend] at hsub
  simp only [Pi.pow_apply, Function.comp_apply] at hsub
  rw [← hsub, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le Real.pi_pos.le]
  apply intervalIntegral.integral_congr
  intro x _
  change v (timePrimitive (ovalDensity a b) 0 x) ^ 4 * ovalDensity a b x = _
  rw [heq]
  change ovalProfile a b (θ (timePrimitive (ovalDensity a b) 0 x)) ^ 4 * ovalDensity a b x = _
  rw [hleft]
  exact ovalProfile_four_mul_density ha hab.le x

/-- A genuine bound on the logarithmic derivative forces every time
required to grow from eta to c to be at least 2 log(c/eta). -/
theorem time_lower_bound_of_logarithmic_speed {v : ℝ → ℝ}
    (hv : Differentiable ℝ v) (hpos : ∀ t, 0 < v t)
    (hspeed : ∀ t, |deriv v t| ≤ v t / 2)
    {η c τ : ℝ} (hη : 0 < η) (hc : 0 < c) (h0 : v 0 = η)
    (hτ : 0 ≤ τ) (hmax : c ≤ v τ) : 2 * Real.log (c / η) ≤ τ := by
  have hd (t : ℝ) : HasDerivAt (fun s => Real.log (v s)) (deriv v t / v t) t :=
    (hv t).hasDerivAt.log (hpos t).ne'
  have hb (t : ℝ) : ‖deriv v t / v t‖ ≤ (1 / 2 : ℝ) := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hpos t)]
    exact (div_le_iff₀ (hpos t)).mpr (by linarith [hspeed t])
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (univ : Set ℝ)) (fun t _ => (hd t).hasDerivWithinAt)
    (fun t _ => hb t) convex_univ (mem_univ (0 : ℝ)) (mem_univ τ)
  simp only [h0, sub_zero, Real.norm_eq_abs, abs_of_nonneg hτ] at hm
  have hlog := Real.log_le_log hc hmax
  rw [Real.log_div hc.ne' hη.ne']
  have hle := le_abs_self (Real.log (v τ) - Real.log η)
  linarith

end Yamabe3.Analysis.Delaunay
