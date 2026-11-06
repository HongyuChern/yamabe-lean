import Yamabe3.Analysis.DelaunayPeriodMass
import Yamabe3.Analysis.DelaunayEnergy

/-!
# The same admissible Cauchy orbit is a phase of a true neck solution

The prescribed solution is not replaced. A genuine neck orbit is constructed,
its actual attained maximum and the intermediate value theorem match the
prescribed positive value, and the conserved energy fixes the velocity up
to sign. Actual IVP uniqueness identifies the prescribed function. Reflection
is removed using the evenness proved from the zero-velocity neck data.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

private theorem affine_radial_deriv {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (σ τ : ℝ) : deriv (fun t => w (σ * t + τ)) = fun t => σ * deriv w (σ * t + τ) := by
  funext t
  have h := ((hw.differentiable (by simp) (σ * t + τ)).hasDerivAt).comp t
    (((hasDerivAt_id t).const_mul σ).add_const τ)
  simpa only [Function.comp_def, id_eq, mul_one, mul_comm] using h.deriv

private theorem affine_radial_ode {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (heq : ∀ t, deriv (deriv w) t = radialForce (w t))
    (σ τ : ℝ) (hσ : σ ^ 2 = 1) :
    ∀ t, deriv (deriv (fun s => w (σ * s + τ))) t = radialForce (w (σ * t + τ)) := by
  intro t
  have hdw := (contDiff_infty_iff_deriv.mp hw).2
  have h := (((hdw.differentiable (by simp) (σ * t + τ)).hasDerivAt).comp t
    (((hasDerivAt_id t).const_mul σ).add_const τ)).const_mul σ
  simp only [Function.comp_def, id_eq, mul_one] at h
  rw [affine_radial_deriv hw σ τ, h.deriv, heq]
  calc
    σ * (radialForce (w (σ * t + τ)) * σ) = σ ^ 2 * radialForce (w (σ * t + τ)) := by ring
    _ = _ := by rw [hσ, one_mul]

/-- Evenness of the actual neck-normalized solution follows from the
polynomial ODE's proved uniqueness, including at the turning point. -/
theorem radial_neck_solution_even {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (heq : ∀ t, deriv (deriv w) t = radialForce (w t))
    (hd0 : deriv w 0 = 0) : ∀ t, w (-t) = w t := by
  let u : ℝ → ℝ := fun t => w (-1 * t + 0)
  have hu : ContDiff ℝ ∞ u := hw.comp ((contDiff_const.mul contDiff_id).add contDiff_const)
  have huEq := affine_radial_ode hw heq (-1) 0 (by norm_num)
  have h0 : u 0 = w 0 := by simp only [u, mul_zero, add_zero]
  have hdu : deriv u 0 = deriv w 0 := by
    rw [affine_radial_deriv hw (-1) 0]
    simp only [mul_zero, add_zero, hd0, mul_zero]
  have hid : u = w := radial_ode_eq_of_initial hu hw huEq heq h0 hdu
  intro t
  simpa only [u, neg_one_mul, add_zero] using congrFun hid t

/-- Exact phase identification for the original solution and a specified
small neck whose energy agrees at time zero. -/
theorem exists_neck_phase_of_cauchy_energy {η : ℝ} (hη : 0 < η)
    (hηsmall : 3 * η ^ 4 < 1) {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hode : ∀ t, deriv (deriv v) t = radialForce (v t))
    (hm : 0 < v 0)
    (henergy : v 0 ^ 2 - v 0 ^ 6 - 4 * deriv v 0 ^ 2 = η ^ 2 * (1 - η ^ 4)) :
    ∃ (w : ℝ → ℝ) (τ : ℝ),
      ContDiff ℝ ∞ w ∧ w 0 = η ∧ deriv w 0 = 0 ∧
      (∀ t, η ≤ w t ∧ w t ≤ 1 ∧ |deriv w t| ≤ w t / 2) ∧
      (∀ t, deriv (deriv w) t = radialForce (w t)) ∧
      v = fun t => w (t + τ) := by
  let a := η ^ 2
  let b := upperSquared a
  have ha : 0 < a := sq_pos_of_pos hη
  have has : 3 * a ^ 2 < 1 := by dsimp only [a]; nlinarith only [hηsmall]
  obtain ⟨hab, _, hlevel⟩ := upperSquared_properties ha has
  have hb : 0 < b := ha.trans hab
  have hfactor : (v 0 ^ 2 - a) * (b - v 0 ^ 2) * (v 0 ^ 2 + a + b) = 4 * deriv v 0 ^ 2 := by
    calc
      _ = (v 0 ^ 2 - v 0 ^ 6 - (a - a ^ 3)) +
          (v 0 ^ 2 - a) * (a ^ 2 + a * b + b ^ 2 - 1) := by ring
      _ = 4 * deriv v 0 ^ 2 := by
        rw [hlevel]
        dsimp only [a]
        nlinarith only [henergy]
  have hlast : 0 < v 0 ^ 2 + a + b := by positivity
  have hlo : a ≤ v 0 ^ 2 := by
    by_contra hn
    have hx : v 0 ^ 2 < a := lt_of_not_ge hn
    have hneg := mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (sub_neg.mpr hx) (sub_pos.mpr (hx.trans hab))) hlast
    rw [hfactor] at hneg
    nlinarith [sq_nonneg (deriv v 0)]
  have hup : v 0 ^ 2 ≤ b := by
    by_contra hn
    have hx : b < v 0 ^ 2 := lt_of_not_ge hn
    have hneg := mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (sub_pos.mpr (hab.trans hx)) (sub_neg.mpr hx)) hlast
    rw [hfactor] at hneg
    nlinarith [sq_nonneg (deriv v 0)]
  have hmlo : η ≤ v 0 := (sq_le_sq₀ hη.le hm.le).mp hlo
  have hmup : v 0 ≤ Real.sqrt b := Real.le_sqrt_of_sq_le hup
  obtain ⟨w, _, _, hw, _, hw0, hwd0, hwb, hwo, hwe, _⟩ :=
    exists_delaunay_neck_solution hη hηsmall
  obtain ⟨_, _, _, _, s, hs, _, hsmax⟩ := exists_neck_period_with_oval_mass hη hηsmall hw hw0 hwd0 hwo
  obtain ⟨τ, _, hτ⟩ := intermediate_value_Icc hs.le hw.continuous.continuousOn
    (show v 0 ∈ Icc (w 0) (w s) by rw [hw0, hsmax]; exact ⟨hmlo, hmup⟩)
  have hdsq : deriv w τ ^ 2 = deriv v 0 ^ 2 := by
    have h := hwe τ
    rw [hτ] at h
    nlinarith only [h, henergy]
  obtain ⟨σ, hσ, hσd⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * deriv w τ = deriv v 0 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hdsq with hd | hd
    · exact ⟨1, Or.inl rfl, by simpa using hd⟩
    · exact ⟨-1, Or.inr rfl, by rw [hd]; ring⟩
  have hσsq : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  let u : ℝ → ℝ := fun t => w (σ * t + τ)
  have hu : ContDiff ℝ ∞ u := hw.comp ((contDiff_const.mul contDiff_id).add contDiff_const)
  have hdu : deriv u 0 = deriv v 0 := by
    rw [affine_radial_deriv hw σ τ]
    simpa only [mul_zero, zero_add] using hσd
  have hid : v = u := radial_ode_eq_of_initial hv hu hode
    (affine_radial_ode hw hwo σ τ hσsq)
    (by simpa only [u, mul_zero, zero_add] using hτ.symm) hdu.symm
  have heven := radial_neck_solution_even hw hwo hwd0
  have hwb' (t : ℝ) : η ≤ w t ∧ w t ≤ 1 ∧ |deriv w t| ≤ w t / 2 :=
    ⟨(hwb t).1, (hwb t).2.1.le, (hwb t).2.2.le⟩
  rcases hσ with rfl | rfl
  · refine ⟨w, τ, hw, hw0, hwd0, hwb', hwo, ?_⟩
    simpa only [u, one_mul] using hid
  · refine ⟨w, -τ, hw, hw0, hwd0, hwb', hwo, ?_⟩
    funext t
    rw [congrFun hid t]
    change w (-1 * t + τ) = w (t + -τ)
    rw [show -1 * t + τ = -(t + -τ) by ring]
    exact heven _

/-- An admissible actual Cauchy orbit is identified, point for point, with
one phase of a normalized small-neck orbit. The neck is constructed from
its true energy; its quantitative square bounds and attained value are
proved, rather than inferred from a module name or a lower-bound field. -/
theorem exists_same_cauchy_orbit_neck_phase {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (hode : ∀ t, deriv (deriv v) t = radialForce (v t))
    (hm : 0 < v 0) {q : ℝ} (hq : 0 < q) (hsmall : q < 3 / 8)
    (henergy : q = v 0 ^ 2 - v 0 ^ 6 - 4 * deriv v 0 ^ 2) :
    ∃ (η : ℝ) (w : ℝ → ℝ) (τ : ℝ),
      0 < η ∧ 3 * η ^ 4 < 1 ∧ η ^ 2 * (1 - η ^ 4) = q ∧
      q ≤ η ^ 2 ∧ η ^ 2 ≤ 2 * q ∧
      ContDiff ℝ ∞ w ∧ w 0 = η ∧ deriv w 0 = 0 ∧
      (∀ t, η ≤ w t ∧ w t ≤ 1 ∧ |deriv w t| ≤ w t / 2) ∧
      (∀ t, deriv (deriv w) t = radialForce (w t)) ∧
      v = (fun t => w (t + τ)) ∧ v (-τ) = η := by
  obtain ⟨a, ha, haHalf, haE, hqa, haq⟩ := exists_squared_neck_of_energy hq hsmall
  let η := Real.sqrt a
  have hη : 0 < η := Real.sqrt_pos.mpr ha
  have hηsq : η ^ 2 = a := Real.sq_sqrt ha.le
  have hηfour : η ^ 4 = a ^ 2 := by rw [show η ^ 4 = (η ^ 2) ^ 2 by ring, hηsq]
  have hηsmall : 3 * η ^ 4 < 1 := by rw [hηfour]; nlinarith
  have hηE : η ^ 2 * (1 - η ^ 4) = q := by rw [hηsq, hηfour]; nlinarith only [haE]
  obtain ⟨w, τ, hw, hw0, hwd0, hwb, hwo, heq⟩ :=
    exists_neck_phase_of_cauchy_energy hη hηsmall hv hode hm (henergy.symm.trans hηE.symm)
  refine ⟨η, w, τ, hη, hηsmall, hηE, ?_, ?_, hw, hw0, hwd0, hwb, hwo, heq, ?_⟩
  · simpa only [hηsq] using hqa
  · simpa only [hηsq] using haq
  · rw [heq]
    simpa only [neg_add_cancel] using hw0

end Yamabe3.Analysis.Delaunay
