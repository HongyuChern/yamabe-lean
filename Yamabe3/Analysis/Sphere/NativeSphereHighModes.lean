import Yamabe3.Analysis.Sphere.NativeSphereSpectralBasis

/-!
# Reconstruction after removing the actual constant and height modes

Zero mean and zero height moments refer to the real round-sphere volume.
They force every native eigenbasis coefficient below six to vanish.  The
remaining genuine angular modes reconstruct the original L2 function.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SphereSpectrum

open Poincare.Geometry.Riemannian.SpaceForm

abbrev HighAngularIndex := {i : AngularIndex // 6 ≤ angularEigenvalue i}

theorem angular_coefficient_zero_of_low_moments (f : AngularL2)
    (hmean : (∫ x, f x ∂(roundSphereMetric 2).volumeMeasure) = 0)
    (hfirst : ∀ a : Ambient 2,
      (∫ x, height a x * f x ∂(roundSphereMetric 2).volumeMeasure) = 0)
    (i : AngularIndex) (hi : angularEigenvalue i < 6) :
    inner ℝ (angularBasis i) f = 0 := by
  rcases angularEigenvalue_zero_two_or_ge_six i with h0 | h2 | h6
  · obtain ⟨c, hc⟩ := angularBasis_zero_is_constant i h0
    rw [L2.inner_def, setIntegral_univ]
    calc
      (∫ x, inner ℝ (angularBasis i x) (f x) ∂(roundSphereMetric 2).volumeMeasure) =
          ∫ x, c * f x ∂(roundSphereMetric 2).volumeMeasure := by
        apply integral_congr_ae
        filter_upwards [hc] with x hx
        rw [hx]
        simp [mul_comm]
      _ = c * (∫ x, f x ∂(roundSphereMetric 2).volumeMeasure) := integral_const_mul _ _
      _ = 0 := by rw [hmean, mul_zero]
  · obtain ⟨a, ha⟩ := angularBasis_two_is_height i h2
    rw [L2.inner_def, setIntegral_univ]
    calc
      (∫ x, inner ℝ (angularBasis i x) (f x) ∂(roundSphereMetric 2).volumeMeasure) =
          ∫ x, height a x * f x ∂(roundSphereMetric 2).volumeMeasure := by
        apply integral_congr_ae
        filter_upwards [ha] with x hx
        rw [hx]
        simp [mul_comm]
      _ = 0 := hfirst a
  · exact (not_lt_of_ge h6 hi).elim

theorem high_angular_modes_reconstruct (f : AngularL2)
    (hmean : (∫ x, f x ∂(roundSphereMetric 2).volumeMeasure) = 0)
    (hfirst : ∀ a : Ambient 2,
      (∫ x, height a x * f x ∂(roundSphereMetric 2).volumeMeasure) = 0) :
    HasSum (fun i : HighAngularIndex => inner ℝ (angularBasis i.val) f • angularBasis i.val) f := by
  have hsupp : Function.support (fun i : AngularIndex => inner ℝ (angularBasis i) f • angularBasis i) ⊆
      {i : AngularIndex | 6 ≤ angularEigenvalue i} := by
    intro i hi
    by_contra hfail
    have hz := angular_coefficient_zero_of_low_moments f hmean hfirst i (lt_of_not_ge hfail)
    exact hi (by change inner ℝ (angularBasis i) f • angularBasis i = 0; rw [hz, zero_smul])
  exact (hasSum_subtype_iff_of_support_subset hsupp).mpr (angularBasis_reconstruct f)

#print axioms angular_coefficient_zero_of_low_moments
#print axioms high_angular_modes_reconstruct

end Yamabe3.Analysis.SphereSpectrum
