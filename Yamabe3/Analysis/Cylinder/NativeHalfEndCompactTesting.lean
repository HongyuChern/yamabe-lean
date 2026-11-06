import Yamabe3.Analysis.Cylinder.NativeContinuousAngularTesting
import Yamabe3.Analysis.Cylinder.CylindricalShellGeometry

/-!
# Actual compact tests for the half-end inverse-square potential

A compact test avoiding the origin lies in one actual logarithmic shell.
The original bounded continuous potential divided by the actual squared
radius becomes a continuous compact function after multiplication by
that test. Its L2 norm is therefore available without imposing global
L2 integrability of the potential times an arbitrary H1 solution.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay UniformElliptic

/-- The actual inverse-square coefficient of the normalized physical
half-end equation. It uses the original potential and original radius. -/
def nativeHalfEndPotentialCoefficient (V : ℝ →ᵇ ℝ) (x : E) : ℝ :=
  V (-Real.log ‖x‖) / ‖x‖ ^ 2

theorem nativeHalfEndPotentialCoefficient_continuousOn (V : ℝ →ᵇ ℝ) :
    ContinuousOn (nativeHalfEndPotentialCoefficient V) ({0}ᶜ : Set E) := by
  intro x hx
  have hx0 : x ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hx
  exact ((V.continuous.continuousAt.comp
    ((Real.continuousAt_log (norm_ne_zero_iff.mpr hx0)).comp continuous_norm.continuousAt).neg).div
      (continuous_norm.continuousAt.pow 2) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx0))).continuousWithinAt

/-- Local continuity is enough once the other factor is an actual
continuous compact test supported inside the open region. -/
theorem integrable_mul_compact_test_of_continuousOn
    {O : Set E} (hO : IsOpen O) {u φ : E → ℝ} (hu : ContinuousOn u O)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ O) :
    Integrable (fun x => u x * φ x) (volume : Measure E) := by
  have hcont : Continuous (fun x => φ x * u x) :=
    (hφ.continuousOn.mul hu).continuous_of_tsupport_subset hO
      (tsupport_mul_subset_left.trans hs)
  have hi : Integrable (fun x => φ x * u x) (volume : Measure E) :=
    hcont.integrable_of_hasCompactSupport hc.mul_right
  simpa only [mul_comm] using hi

/-- Every compact set avoiding zero has one genuine containing shell.
No shell depending on the approximation index is selected. -/
theorem exists_cylinderShell_containing_compact
    {K : Set E} (hK : IsCompact K) (hK0 : (0 : E) ∉ K) :
    ∃ a b : ℝ, K ⊆ cylinderShell a b := by
  have hcont : ContinuousOn (fun x : E => -Real.log ‖x‖) K := by
    intro x hx
    have hx0 : x ≠ 0 := fun h => hK0 (h ▸ hx)
    exact ((Real.continuousAt_log (norm_ne_zero_iff.mpr hx0)).comp
      continuous_norm.continuousAt).neg.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨-C - 1, C + 1, ?_⟩
  intro x hx
  have hx0 : x ≠ 0 := fun h => hK0 (h ▸ hx)
  have hb : |-Real.log ‖x‖| ≤ C := by simpa only [Real.norm_eq_abs] using hC x hx
  apply cylinderAnnulus_subset_shell _ _
  exact mem_cylinderAnnulus_of_log_norm hx0
    (by linarith only [(abs_le.mp hb).1]) (by linarith only [(abs_le.mp hb).2])

/-- Multiplying the true singular coefficient by an actual compact
test removes the singularity by support, with the same product function. -/
theorem nativeHalfEndPotentialCoefficient_mul_test_continuous
    (V : ℝ →ᵇ ℝ) {φ : E → ℝ} (hφ : Continuous φ)
    (hzero : (0 : E) ∉ tsupport φ) :
    Continuous (fun x => nativeHalfEndPotentialCoefficient V x * φ x) := by
  have hs : tsupport φ ⊆ ({0}ᶜ : Set E) := by
    intro x hx
    exact fun hx0 => hzero (by simpa only [mem_singleton_iff] using hx0 ▸ hx)
  exact ((nativeHalfEndPotentialCoefficient_continuousOn V).mul hφ.continuousOn).continuous_of_tsupport_subset
    isClosed_singleton.isOpen_compl
      (tsupport_mul_subset_right.trans hs)

theorem nativeHalfEndPotentialCoefficient_mul_test_memLp
    (V : ℝ →ᵇ ℝ) {φ : E → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hzero : (0 : E) ∉ tsupport φ) :
    MemLp (fun x => nativeHalfEndPotentialCoefficient V x * φ x) 2 volume :=
  (nativeHalfEndPotentialCoefficient_mul_test_continuous V hφ hzero).memLp_of_hasCompactSupport
    hc.mul_left

/-- Actual full-space pairings with a compact test use the same fixed
shell on both sides. The infinite source and its finite projections are
not replaced by chosen unrelated Lp representatives. -/
theorem native_projected_halfEnd_physicalForcing_compact_pairing_tendsto
    {s : ℕ → Finset AngularIndex} (hs : Tendsto s atTop atTop)
    {U : ℝ → AngularL2} (hU : Continuous U)
    {z : ℝ × S → ℝ} (hz : Measurable z)
    (hae : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ))
    {φ : E → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hzero : (0 : E) ∉ tsupport φ) :
    Tendsto (fun n => ∫ x : E,
      physicalForcing (fun p => Real.exp (-2 * p.1) * projectedAngular (s n) U p) x * φ x)
      atTop (𝓝 (∫ x : E,
        physicalForcing (fun p => Real.exp (-2 * p.1) * z p) x * φ x)) := by
  obtain ⟨a, b, hK⟩ := exists_cylinderShell_containing_compact hc hzero
  have h := native_projected_halfEnd_physicalForcing_pairing_tendsto
    hs hU hz hae a b ((hφ.memLp_of_hasCompactSupport hc).restrict _)
  have he (f : E → ℝ) :
      (∫ x in cylinderShell a b, f x * φ x) = ∫ x : E, f x * φ x := by
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hK ht)), mul_zero]
  simpa only [he] using h

#check @nativeHalfEndPotentialCoefficient_continuousOn
#check @integrable_mul_compact_test_of_continuousOn
#check @exists_cylinderShell_containing_compact
#check @nativeHalfEndPotentialCoefficient_mul_test_continuous
#check @nativeHalfEndPotentialCoefficient_mul_test_memLp
#check @native_projected_halfEnd_physicalForcing_compact_pairing_tendsto
#print axioms nativeHalfEndPotentialCoefficient_continuousOn
#print axioms integrable_mul_compact_test_of_continuousOn
#print axioms exists_cylinderShell_containing_compact
#print axioms nativeHalfEndPotentialCoefficient_mul_test_continuous
#print axioms nativeHalfEndPotentialCoefficient_mul_test_memLp
#print axioms native_projected_halfEnd_physicalForcing_compact_pairing_tendsto

end Yamabe3.Analysis.SpherePolar
