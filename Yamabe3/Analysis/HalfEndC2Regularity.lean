import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Actual C2 regularity from the same first-order Cauchy data

The value, its first derivative, and the continuous second derivative
are actual functions on an open set. Derivative uniqueness identifies
the classical derivative with the supplied first derivative there.
This needs only a continuous forcing in a second-order scalar equation;
no global smooth extension or smoothness of the source is assumed.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped ContDiff

namespace Yamabe3.Analysis.Delaunay

/-- A continuous actual derivative gives C1 regularity on the same open
set, without requirements on the complement. -/
theorem contDiffOn_one_of_continuous_derivative
    {O : Set ℝ} (hO : IsOpen O) (u du : ℝ → ℝ)
    (hdu : ContinuousOn du O)
    (hd : ∀ t ∈ O, HasDerivAt u (du t) t) :
    ContDiffOn ℝ 1 u O := by
  apply (contDiffOn_one_iff_derivWithin hO.uniqueDiffOn).mpr
  refine ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt, ?_⟩
  apply hdu.congr
  intro t ht
  exact (hd t ht).hasDerivWithinAt.derivWithin (hO.uniqueDiffOn t ht)

/-- Genuine first and second derivative data imply actual C2 regularity
of the same original function on the open domain. -/
theorem contDiffOn_two_of_continuous_second_derivative
    {O : Set ℝ} (hO : IsOpen O) (u du ddu : ℝ → ℝ)
    (hddu : ContinuousOn ddu O)
    (hd : ∀ t ∈ O, HasDerivAt u (du t) t)
    (hdd : ∀ t ∈ O, HasDerivAt du (ddu t) t) :
    ContDiffOn ℝ 2 u O := by
  have hdu : ContDiffOn ℝ 1 du O :=
    contDiffOn_one_of_continuous_derivative hO du ddu hddu hdd
  rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen hO]
  refine ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  exact hdu.congr (fun t ht => (hd t ht).deriv)

/-- A scalar half-end equation with continuous potential and source
produces C2 regularity on the actual positive half-line. -/
theorem halfEnd_contDiffOn_two_of_cauchy_equation
    (z dz q f : ℝ → ℝ)
    (hz : ContinuousOn z (Ioi 0)) (hq : ContinuousOn q (Ioi 0))
    (hf : ContinuousOn f (Ioi 0))
    (hd : ∀ t : ℝ, 0 < t → HasDerivAt z (dz t) t)
    (hdd : ∀ t : ℝ, 0 < t → HasDerivAt dz (q t * z t + f t) t) :
    ContDiffOn ℝ 2 z (Ioi 0) :=
  contDiffOn_two_of_continuous_second_derivative isOpen_Ioi z dz
    (fun t => q t * z t + f t) ((hq.mul hz).add hf) hd hdd

#print axioms contDiffOn_one_of_continuous_derivative
#print axioms contDiffOn_two_of_continuous_second_derivative
#print axioms halfEnd_contDiffOn_two_of_cauchy_equation

end Yamabe3.Analysis.Delaunay
