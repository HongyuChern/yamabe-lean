import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar half-end coercivity from the actual equation and decay

The curve and its first derivative are retained as actual functions. At
the entrance the first derivative is the right derivative on `Ici 0`;
no derivative of an arbitrarily chosen negative-time extension is used.
The equation for the first derivative is required only at positive times.

On each finite interval the genuine fundamental theorem of calculus
identifies an integral of completed squares with the endpoint energy.
Positivity of this integral and decay of both actual curves then give
the entrance coercivity. No energy inequality is an input.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open Set Filter MeasureTheory
open scoped Topology

namespace Yamabe3.Analysis.Delaunay

/-- The exact finite-interval identity for the same scalar curve and its
actual first derivative. The second derivative is used only in `(0,T)`. -/
theorem halfEnd_scalar_square_completion_integral
    (z dz q : ℝ → ℝ)
    (hz : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt z (dz t) (Ici 0) t)
    (hdz : ContinuousOn dz (Ici 0)) (hq : ContinuousOn q (Ici 0))
    (hode : ∀ t : ℝ, 0 < t → HasDerivAt dz (q t * z t) t)
    (c T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, (dz t + c * z t) ^ 2 + (q t - c ^ 2) * z t ^ 2) =
      (z T * dz T + c * z T ^ 2) - (z 0 * dz 0 + c * z 0 ^ 2) := by
  have hzc : ContinuousOn z (Ici 0) := fun t ht => (hz t ht).continuousWithinAt
  have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
  have henergy : ContinuousOn (fun t => z t * dz t + c * z t ^ 2) (Icc (0 : ℝ) T) :=
    ((hzc.mul hdz).add ((hzc.pow 2).const_mul c)).mono hsub
  have hintegrand : ContinuousOn
      (fun t => (dz t + c * z t) ^ 2 + (q t - c ^ 2) * z t ^ 2)
        (Icc (0 : ℝ) T) :=
    (((hdz.add (hzc.const_mul c)).pow 2).add
      ((hq.sub continuousOn_const).mul (hzc.pow 2))).mono hsub
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT henergy _
    (hintegrand.intervalIntegrable_of_Icc hT)
  intro t ht
  have hd : HasDerivAt z (dz t) t := (hz t ht.1.le).hasDerivAt (Ici_mem_nhds ht.1)
  have h := (hd.mul (hode t ht.1)).add ((hd.pow 2).const_mul c)
  apply h.congr_deriv
  ring

/-- The finite endpoint energy inequality follows from the nonnegative
completed-square integral, rather than being supplied by the caller. -/
theorem halfEnd_scalar_boundary_energy_le
    (z dz q : ℝ → ℝ)
    (hz : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt z (dz t) (Ici 0) t)
    (hdz : ContinuousOn dz (Ici 0)) (hq : ContinuousOn q (Ici 0))
    (hode : ∀ t : ℝ, 0 < t → HasDerivAt dz (q t * z t) t)
    (c : ℝ) (hgap : ∀ t : ℝ, 0 ≤ t → c ^ 2 ≤ q t)
    (T : ℝ) (hT : 0 ≤ T) :
    z 0 * dz 0 + c * z 0 ^ 2 ≤ z T * dz T + c * z T ^ 2 := by
  have hnonneg : 0 ≤
      ∫ t in (0 : ℝ)..T, (dz t + c * z t) ^ 2 + (q t - c ^ 2) * z t ^ 2 := by
    apply intervalIntegral.integral_nonneg hT
    intro t ht
    exact add_nonneg (sq_nonneg _) (mul_nonneg
      (sub_nonneg.mpr (hgap t ht.1)) (sq_nonneg _))
  rw [halfEnd_scalar_square_completion_integral z dz q hz hdz hq hode c T hT] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Decay of the same value and first derivative closes the boundary term
at infinity and gives actual entrance coercivity. The first derivative
at zero is the right derivative specified by `hz`, not a free boundary
quantity. No infinite-interval integration-by-parts premise is used. -/
theorem halfEnd_scalar_coercivity
    (z dz q : ℝ → ℝ)
    (hz : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt z (dz t) (Ici 0) t)
    (hdz : ContinuousOn dz (Ici 0)) (hq : ContinuousOn q (Ici 0))
    (hode : ∀ t : ℝ, 0 < t → HasDerivAt dz (q t * z t) t)
    (c : ℝ) (hgap : ∀ t : ℝ, 0 ≤ t → c ^ 2 ≤ q t)
    (hzdecay : Tendsto z atTop (𝓝 0)) (hdzdecay : Tendsto dz atTop (𝓝 0)) :
    c * z 0 ^ 2 ≤ -(dz 0) * z 0 := by
  have hlim : Tendsto (fun T => z T * dz T + c * z T ^ 2) atTop (𝓝 0) := by
    simpa using (hzdecay.mul hdzdecay).add ((hzdecay.pow 2).const_mul c)
  have hboundary : z 0 * dz 0 + c * z 0 ^ 2 ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact halfEnd_scalar_boundary_energy_le z dz q hz hdz hq hode c hgap T hT
  nlinarith only [hboundary]

#print axioms halfEnd_scalar_square_completion_integral
#print axioms halfEnd_scalar_boundary_energy_le
#print axioms halfEnd_scalar_coercivity

end Yamabe3.Analysis.Delaunay
