import Yamabe3.Analysis.DelaunayEnergy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Actual radial profiles from the constructed Delaunay orbit

The profile is the genuine function exp(-log(r)/2)*v(tau-log(r)).
Its first and second derivatives are computed at every positive radius,
including the radial ODE and the cylindrical lower bound. No geometric
Laplacian is redefined by this scalar calculation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace Yamabe3.Analysis.Delaunay

def radialScale (r : ℝ) : ℝ := Real.exp (-Real.log r / 2)

def radialProfile (v : ℝ → ℝ) (τ r : ℝ) : ℝ :=
  radialScale r * v (τ - Real.log r)

theorem radialScale_pos (r : ℝ) : 0 < radialScale r := Real.exp_pos _

theorem radialScale_sq {r : ℝ} (hr : 0 < r) : radialScale r ^ 2 = r⁻¹ := by
  rw [radialScale, pow_two, ← Real.exp_add,
    show -Real.log r / 2 + -Real.log r / 2 = -Real.log r by ring,
    Real.exp_neg, Real.exp_log hr]

theorem radialScale_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt radialScale (-radialScale r / (2 * r)) r := by
  have h := (((Real.hasDerivAt_log hr.ne').neg).div_const 2).exp
  convert! h using 1
  unfold radialScale
  simp only [Pi.neg_apply, neg_div]
  field_simp

theorem radialProfile_contDiffOn {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (τ : ℝ) :
    ContDiffOn ℝ ∞ (radialProfile v τ) (Ioi 0) := by
  intro r hr
  apply ContDiffAt.contDiffWithinAt
  have hl : ContDiffAt ℝ ∞ Real.log r := Real.contDiffAt_log.mpr hr.ne'
  exact ((hl.neg.div_const 2).exp).mul (hv.contDiffAt.comp r (contDiffAt_const.sub hl))

theorem radialProfile_hasDerivAt {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (τ : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (radialProfile v τ)
      (-(radialScale r / r) * (v (τ - Real.log r) / 2 + deriv v (τ - Real.log r))) r := by
  have ht := (Real.hasDerivAt_log hr.ne').const_sub τ
  have hvd := (hv.differentiable (by simp) (τ - Real.log r)).hasDerivAt.comp r ht
  have h := (radialScale_hasDerivAt hr).mul hvd
  convert! h using 1
  simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply]
  field_simp
  ring

theorem radialProfile_deriv {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (τ : ℝ) {r : ℝ} (hr : 0 < r) :
    deriv (radialProfile v τ) r =
      -(radialScale r / r) * (v (τ - Real.log r) / 2 + deriv v (τ - Real.log r)) :=
  (radialProfile_hasDerivAt hv τ hr).deriv

theorem radialProfile_second {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (τ : ℝ) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (radialProfile v τ)) r =
      radialScale r / r ^ 2 *
        (deriv (deriv v) (τ - Real.log r) + 2 * deriv v (τ - Real.log r) +
          3 * v (τ - Real.log r) / 4) := by
  have ht := (Real.hasDerivAt_log hr.ne').const_sub τ
  have hvd := (hv.differentiable (by simp) (τ - Real.log r)).hasDerivAt.comp r ht
  have hvdd := ((hv.deriv' (n := ∞)).differentiable (by simp)
    (τ - Real.log r)).hasDerivAt.comp r ht
  have hp := ((radialScale_hasDerivAt hr).mul (hasDerivAt_inv hr.ne')).neg
  have h := hp.mul ((hvd.div_const 2).add hvdd)
  have hd : HasDerivAt
      (fun s => -(radialScale s * s⁻¹) * (v (τ - Real.log s) / 2 + deriv v (τ - Real.log s)))
      (radialScale r / r ^ 2 *
        (deriv (deriv v) (τ - Real.log r) + 2 * deriv v (τ - Real.log r) +
          3 * v (τ - Real.log r) / 4)) r := by
    convert! h using 1
    simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply]
    field_simp [hr.ne']
    ring
  have heq : deriv (radialProfile v τ) =ᶠ[𝓝 r]
      (fun s => -(radialScale s * s⁻¹) * (v (τ - Real.log s) / 2 + deriv v (τ - Real.log s))) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    simpa only [div_eq_mul_inv] using radialProfile_deriv hv τ hs
  exact (hd.congr_of_eventuallyEq heq).deriv

theorem radialProfile_radial_equation {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hODE : ∀ t, deriv (deriv v) t = v t / 4 - 3 * v t ^ 5 / 4)
    (τ : ℝ) {r : ℝ} (hr : 0 < r) :
    -8 * (deriv (deriv (radialProfile v τ)) r +
      2 / r * deriv (radialProfile v τ) r) = 6 * radialProfile v τ r ^ 5 := by
  have hs4 : radialScale r ^ 4 = (r ^ 2)⁻¹ := by
    rw [show radialScale r ^ 4 = (radialScale r ^ 2) ^ 2 by ring, radialScale_sq hr, inv_pow]
  rw [radialProfile_second hv τ hr, radialProfile_deriv hv τ hr, hODE]
  unfold radialProfile
  rw [mul_pow, show radialScale r ^ 5 = radialScale r * radialScale r ^ 4 by ring, hs4]
  field_simp [hr.ne']
  ring

theorem radialProfile_cylindrical_lower_bound {v : ℝ → ℝ} {η : ℝ}
    (hη : 0 < η) (hmin : ∀ t, η ≤ v t) (τ : ℝ) {r : ℝ} (hr : 0 < r) :
    0 < radialProfile v τ r ∧ η ^ 2 * r⁻¹ ≤ radialProfile v τ r ^ 2 := by
  have hv := hη.trans_le (hmin (τ - Real.log r))
  refine ⟨mul_pos (radialScale_pos r) hv, ?_⟩
  rw [radialProfile, mul_pow, radialScale_sq hr]
  have hsq := (sq_le_sq₀ hη.le hv.le).mpr (hmin (τ - Real.log r))
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsq (inv_pos.mpr hr).le

#print axioms radialProfile_contDiffOn
#print axioms radialProfile_radial_equation
#print axioms radialProfile_cylindrical_lower_bound

end Yamabe3.Analysis.Delaunay
