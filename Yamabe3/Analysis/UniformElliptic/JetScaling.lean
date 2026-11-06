import Yamabe3.Analysis.UniformElliptic.LocalUniformJet

/-!
# Exact local higher-jet dilation

The genuine local smooth function is first extended by an actual cutoff near
the evaluation point. Global chain rules are applied to that proved extension
and transferred back by equality of germs. No global smoothness of the Green
correction at its pole is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set MeasureTheory Filter Metric
open scoped ContDiff Topology

namespace Yamabe3.Analysis.UniformElliptic

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem iteratedFDeriv_centered_comp_smul
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (m : ℕ) (hm : m ≠ 0)
    (r b : ℝ) (x : E) :
    iteratedFDeriv ℝ m (fun y => u (r • y) - b) x =
      r ^ m • iteratedFDeriv ℝ m u (r • x) := by
  have hun : ContDiff ℝ m u := hu.of_le (by exact_mod_cast le_top)
  have hc : ContDiff ℝ m (fun y : E => u (r • y)) :=
    hun.comp (contDiff_id.const_smul r)
  rw [fun_iteratedFDeriv_sub_apply hc.contDiffAt contDiffAt_const,
    iteratedFDeriv_const_of_ne hm b, Pi.zero_apply, sub_zero,
    iteratedFDeriv_comp_const_smul r hun]

/-- Exact dilation and centering of every positive-order jet of a function
smooth only in an actual open neighborhood of the image point. -/
theorem iteratedFDeriv_local_centered_dilation
    {O : Set E} (hO : IsOpen O) {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u O)
    (m : ℕ) (hm : m ≠ 0) (r b : ℝ) (x : E) (hx : r • x ∈ O) :
    iteratedFDeriv ℝ m (fun y => u (r • y) - b) x =
      r ^ m • iteratedFDeriv ℝ m u (r • x) := by
  obtain ⟨v, hv, _, hve⟩ := exists_smooth_compact_extension_near_compact
    hO (isCompact_singleton : IsCompact ({r • x} : Set E))
    (singleton_subset_iff.mpr hx) hu
  have hvu : v =ᶠ[𝓝 (r • x)] u := hve (r • x) (mem_singleton _)
  have hc : (fun y : E => v (r • y) - b) =ᶠ[𝓝 x] (fun y => u (r • y) - b) := by
    filter_upwards [hvu.comp_tendsto (continuous_const_smul r).continuousAt] with y hy
    change v (r • y) = u (r • y) at hy
    rw [hy]
  rw [← (hc.iteratedFDeriv ℝ m).self_of_nhds,
    iteratedFDeriv_centered_comp_smul hv m hm r b x,
    (hvu.iteratedFDeriv ℝ m).self_of_nhds]

/-- The positive-scale norm formula needed to return uniform annular jets
to the true derivatives at a point tending to the pole. -/
theorem norm_iteratedFDeriv_local_centered_dilation
    {O : Set E} (hO : IsOpen O) {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u O)
    (m : ℕ) (hm : m ≠ 0) {r : ℝ} (hr : 0 ≤ r) (b : ℝ)
    (x : E) (hx : r • x ∈ O) :
    ‖iteratedFDeriv ℝ m (fun y => u (r • y) - b) x‖ =
      r ^ m * ‖iteratedFDeriv ℝ m u (r • x)‖ := by
  rw [iteratedFDeriv_local_centered_dilation hO hu m hm r b x hx,
    norm_smul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hr]

#print axioms iteratedFDeriv_local_centered_dilation
#print axioms norm_iteratedFDeriv_local_centered_dilation

end Yamabe3.Analysis.UniformElliptic
