import Yamabe3.Analysis.HighModeCoercivityConstants

/-!
# Removing the actual half-end weight with a retained source

This is the forced version of the already proved physical derivative
identity. The source is the same scalar source in the weighted equation;
its physical coefficient is exactly exp(-2t), not a new normalization.
The actual first derivative of the same physical curve is identified by
derivative uniqueness before the second derivative is taken.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set Filter
open scoped Topology

namespace Yamabe3.Analysis.Delaunay

theorem halfEnd_expTwo_forced_physical_derivative_equation
    (y z dz q f : ℝ → ℝ)
    (hzy : ∀ t : ℝ, 0 < t → z t = Real.exp (-2 * t) * y t)
    (hz : ∀ t : ℝ, 0 < t → HasDerivAt z (dz t) t)
    (hy : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ y t ∧
      HasDerivAt (deriv y) (4 * deriv y t + (q t - 4) * y t + f t) t)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt dz (q t * z t + Real.exp (-2 * t) * f t) t := by
  let e : ℝ → ℝ := fun s => Real.exp (-2 * s)
  have he (s : ℝ) : HasDerivAt e (-2 * e s) s := by
    apply (((hasDerivAt_id s).const_mul (-2)).exp).congr_deriv
    dsimp only [e, id_eq]
    ring
  have hdz (s : ℝ) (hs : 0 < s) : dz s = e s * (deriv y s - 2 * y s) := by
    have heq : z =ᶠ[𝓝 s] fun r => e r * y r := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
      exact hzy r hr
    have hd := ((he s).mul (hy s hs).1.hasDerivAt).congr_of_eventuallyEq heq
    calc
      dz s = (-2 * e s) * y s + e s * deriv y s := (hz s hs).unique hd
      _ = e s * (deriv y s - 2 * y s) := by ring
  have hdeq : dz =ᶠ[𝓝 t] fun s => e s * (deriv y s - 2 * y s) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact hdz s hs
  have hd := (he t).mul ((hy t ht).2.sub ((hy t ht).1.hasDerivAt.const_mul 2))
  apply (hd.congr_of_eventuallyEq hdeq).congr_deriv
  rw [hzy t ht]
  dsimp only [e, Pi.sub_apply]
  ring

#print axioms halfEnd_expTwo_forced_physical_derivative_equation

end Yamabe3.Analysis.Delaunay
