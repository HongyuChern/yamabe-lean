import Yamabe3.Analysis.HalfEndScalarCoercivity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Rate-sensitive decay of the same half-line curve, obtained from the
actual equation and its two tails. The rate is the square-root coercivity
gap, not a freely supplied decay estimate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology
namespace Yamabe3.Analysis.Delaunay

theorem halfEnd_scalar_coercivity_at
    (z dz q : ℝ → ℝ)
    (hz : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt z (dz t) (Ici 0) t)
    (hdz : ContinuousOn dz (Ici 0)) (hq : ContinuousOn q (Ici 0))
    (hode : ∀ t : ℝ, 0 < t → HasDerivAt dz (q t * z t) t)
    (c : ℝ) (hgap : ∀ t : ℝ, 0 ≤ t → c ^ 2 ≤ q t)
    (hzdecay : Tendsto z atTop (𝓝 0)) (hdzdecay : Tendsto dz atTop (𝓝 0))
    (T : ℝ) (hT : 0 ≤ T) :
    c * z T ^ 2 ≤ -(dz T) * z T := by
  have hmap : MapsTo (fun s : ℝ => T + s) (Ici 0) (Ici 0) :=
    fun s hs => add_nonneg hT hs
  have hshift : Tendsto (fun s : ℝ => T + s) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b - T)] with s hs
    linarith
  have h := halfEnd_scalar_coercivity (fun s => z (T+s)) (fun s => dz (T+s))
    (fun s => q (T+s))
    (fun s hs => by
      simpa only [Function.comp_def, mul_one] using (hz (T+s) (add_nonneg hT hs)).comp s
        ((hasDerivAt_id s).const_add T).hasDerivWithinAt hmap)
    (hdz.comp (continuous_const.add continuous_id).continuousOn hmap)
    (hq.comp (continuous_const.add continuous_id).continuousOn hmap)
    (fun s hs => by
      simpa only [Function.comp_def, mul_one] using (hode (T+s) (by linarith)).comp s ((hasDerivAt_id s).const_add T))
    c (fun s hs => hgap (T+s) (add_nonneg hT hs))
    (hzdecay.comp hshift) (hdzdecay.comp hshift)
  simpa only [add_zero] using h

/-- The square of the actual field decays with the actual coercivity rate.
This retains the original field even when it changes sign. -/
theorem halfEnd_scalar_exponential_square_bound
    (z dz q : ℝ → ℝ)
    (hz : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt z (dz t) (Ici 0) t)
    (hdz : ContinuousOn dz (Ici 0)) (hq : ContinuousOn q (Ici 0))
    (hode : ∀ t : ℝ, 0 < t → HasDerivAt dz (q t * z t) t)
    (c : ℝ) (hgap : ∀ t : ℝ, 0 ≤ t → c ^ 2 ≤ q t)
    (hzdecay : Tendsto z atTop (𝓝 0)) (hdzdecay : Tendsto dz atTop (𝓝 0))
    (t : ℝ) (ht : 0 ≤ t) :
    z t ^ 2 ≤ Real.exp (-2 * c * t) * z 0 ^ 2 := by
  have hzc : ContinuousOn z (Ici 0) := fun s hs => (hz s hs).continuousWithinAt
  let f : ℝ → ℝ := fun s => Real.exp (2*c*s) * z s ^ 2
  let df : ℝ → ℝ := fun s => Real.exp (2*c*s) * (2*c*z s ^ 2 + 2*z s*dz s)
  have hfc : ContinuousOn f (Ici 0) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
      (hzc.pow 2)
  have hdf (s : ℝ) (hs : 0 < s) : HasDerivAt f (df s) s := by
    have hd := (hz s hs.le).hasDerivAt (Ici_mem_nhds hs)
    have h := (((hasDerivAt_id s).const_mul (2*c)).exp).mul (hd.pow 2)
    apply h.congr_deriv
    dsimp [df]
    ring
  have hanti : AntitoneOn f (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ)) hfc
      (f' := df)
    · intro s hs
      rw [interior_Ici] at hs
      exact (hdf s hs).hasDerivWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have h := halfEnd_scalar_coercivity_at z dz q hz hdz hq hode c hgap
        hzdecay hdzdecay s hs.le
      dsimp only [df]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
      nlinarith only [h]
  have hle : Real.exp (2*c*t) * z t ^ 2 ≤ z 0 ^ 2 := by
    simpa [f] using hanti (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr ht) ht
  have h := mul_le_mul_of_nonneg_left hle (Real.exp_nonneg (-2*c*t))
  have he : Real.exp (-2*c*t) * Real.exp (2*c*t) = 1 := by
    rw [← Real.exp_add, show -2*c*t + 2*c*t = 0 by ring, Real.exp_zero]
  simpa only [← mul_assoc, he, one_mul] using h

#print axioms halfEnd_scalar_coercivity_at
#print axioms halfEnd_scalar_exponential_square_bound
end Yamabe3.Analysis.Delaunay
