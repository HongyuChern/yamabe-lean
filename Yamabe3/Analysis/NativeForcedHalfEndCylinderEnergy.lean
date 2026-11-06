import Yamabe3.Analysis.NativeForcedHalfEndAngularEnergy
import Yamabe3.Analysis.NativeForcedHalfEndDerivativeOperator

/-!
# Actual time-integrated energy of the forced half-end

The previously constructed physical H1 representative and the actual
strong AngularL2 time derivative both decay as `exp (-2*t)`.  The exact
integral of `exp (-4*t)` produces their genuine L2 membership on the
closed positive half-line and a quantitative full time-energy estimate.

This file concerns those original Hilbert-valued curves.  It does not
identify a new Euclidean Sobolev representative or a geometric conormal
trace merely from this estimate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

open SphereSpectrum

/-- The exact square-integral consequence of the actual common
`exp(2t)` bound, including the entrance in the integration domain. -/
theorem halfEnd_memLp_two_and_integral_norm_sq_of_expTwo_bound
    {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (hf : Continuous f) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t : ℝ, 0 ≤ t → Real.exp (2 * t) * ‖f t‖ ≤ C) :
    MemLp f 2 (volume.restrict (Ici 0)) ∧
      (∫ t in Ici (0 : ℝ), ‖f t‖ ^ 2) ≤ C ^ 2 / 4 := by
  have hpoint (t : ℝ) (ht : 0 ≤ t) :
      ‖f t‖ ^ 2 ≤ Real.exp (-4 * t) * C ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (hbound t ht) (Real.exp_pos (-2 * t)).le
    have he : Real.exp (-2 * t) * Real.exp (2 * t) = 1 := by
      rw [← Real.exp_add, show -2 * t + 2 * t = 0 by ring, Real.exp_zero]
    have hn : ‖f t‖ ≤ Real.exp (-2 * t) * C := by
      simpa only [← mul_assoc, he, one_mul] using h
    have hs : ‖f t‖ ^ 2 ≤ (Real.exp (-2 * t) * C) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le hC)).mpr hn
    have he2 : Real.exp (-2 * t) ^ 2 = Real.exp (-4 * t) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa only [mul_pow, he2] using hs
  have hmajor : IntegrableOn (fun t : ℝ => Real.exp (-4 * t) * C ^ 2) (Ici 0) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      ((integrableOn_exp_mul_Ioi (by norm_num : (-4 : ℝ) < 0) 0).mul_const (C ^ 2))
  have hsquare : IntegrableOn (fun t : ℝ => ‖f t‖ ^ 2) (Ici 0) := by
    apply hmajor.mono' (hf.norm.pow 2).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    change ‖‖f t‖ ^ 2‖ ≤ Real.exp (-4 * t) * C ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpoint t ht
  refine ⟨(memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hsquare, ?_⟩
  calc
    _ ≤ ∫ t in Ici (0 : ℝ), Real.exp (-4 * t) * C ^ 2 := by
      apply integral_mono_ae hsquare hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact hpoint t ht
    _ = C ^ 2 / 4 := by
      rw [integral_Ici_eq_integral_Ioi, integral_mul_const,
        integral_exp_mul_Ioi (by norm_num : (-4 : ℝ) < 0) 0]
      norm_num <;> ring

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The original physical curve, in its actually constructed H1
representative, is square integrable over the entire half-line. -/
theorem nativeHalfHighDirichletPhysicalEnergy_memLp
    (F : ℝ≥0 →ᵇ AngularL2) :
    MemLp (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F)
      2 (volume.restrict (Ici 0)) :=
  (halfEnd_memLp_two_and_integral_norm_sq_of_expTwo_bound
    (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F)
    (nativeHalfHighDirichletPhysicalEnergy_continuous hκ0 hκ1 V hV hV0 F)
    (nativeHalfHighDirichletEnergyBound κ V * ‖F‖)
    (mul_nonneg (nativeHalfHighDirichletEnergyBound_nonneg hκ1 V) (norm_nonneg F))
    (fun t _ht => nativeHalfHighDirichletPhysicalEnergy_weighted_norm_le
      hκ0 hκ1 V hV hV0 F t)).1

theorem nativeHalfHighDirichletPhysicalEnergy_integral_norm_sq_le
    (F : ℝ≥0 →ᵇ AngularL2) :
    (∫ t in Ici (0 : ℝ),
      ‖nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F t‖ ^ 2) ≤
        nativeHalfHighDirichletEnergyBound κ V ^ 2 * ‖F‖ ^ 2 / 4 := by
  simpa only [mul_pow] using
    (halfEnd_memLp_two_and_integral_norm_sq_of_expTwo_bound
      (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F)
      (nativeHalfHighDirichletPhysicalEnergy_continuous hκ0 hκ1 V hV hV0 F)
      (nativeHalfHighDirichletEnergyBound κ V * ‖F‖)
      (mul_nonneg (nativeHalfHighDirichletEnergyBound_nonneg hκ1 V) (norm_nonneg F))
      (fun t _ht => nativeHalfHighDirichletPhysicalEnergy_weighted_norm_le
        hκ0 hκ1 V hV hV0 F t)).2

/-- The same actual strong time derivative is globally square integrable. -/
theorem nativeHalfHighDirichletPhysicalDerivative_memLp
    (F : ℝ≥0 →ᵇ AngularL2) :
    MemLp (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F)
      2 (volume.restrict (Ici 0)) :=
  (halfEnd_memLp_two_and_integral_norm_sq_of_expTwo_bound
    (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F)
    (nativeHalfHighDirichletPhysicalDerivative_continuous hκ0 hκ1 V hV hV0 F)
    (nativeHalfHighDirichletDerivativeBound κ V * ‖F‖)
    (mul_nonneg (nativeHalfHighDirichletDerivativeBound_nonneg hκ1 V) (norm_nonneg F))
    (nativeHalfHighDirichletPhysicalDerivative_weighted_norm_le hκ0 hκ1 V hV hV0 F)).1

theorem nativeHalfHighDirichletPhysicalDerivative_integral_norm_sq_le
    (F : ℝ≥0 →ᵇ AngularL2) :
    (∫ t in Ici (0 : ℝ),
      ‖nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t‖ ^ 2) ≤
        nativeHalfHighDirichletDerivativeBound κ V ^ 2 * ‖F‖ ^ 2 / 4 := by
  simpa only [mul_pow] using
    (halfEnd_memLp_two_and_integral_norm_sq_of_expTwo_bound
      (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F)
      (nativeHalfHighDirichletPhysicalDerivative_continuous hκ0 hκ1 V hV hV0 F)
      (nativeHalfHighDirichletDerivativeBound κ V * ‖F‖)
      (mul_nonneg (nativeHalfHighDirichletDerivativeBound_nonneg hκ1 V) (norm_nonneg F))
      (nativeHalfHighDirichletPhysicalDerivative_weighted_norm_le hκ0 hκ1 V hV hV0 F)).2

/-- A full time-energy estimate for the original forced curve and its
actual strong derivative, with one constant before the source. -/
theorem nativeHalfHighDirichletPhysical_total_energy_le
    (F : ℝ≥0 →ᵇ AngularL2) :
    IntegrableOn (fun t : ℝ =>
      ‖nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F t‖ ^ 2 +
        ‖nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t‖ ^ 2) (Ici 0) ∧
    (∫ t in Ici (0 : ℝ),
      ‖nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F t‖ ^ 2 +
        ‖nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t‖ ^ 2) ≤
      (nativeHalfHighDirichletEnergyBound κ V ^ 2 +
        nativeHalfHighDirichletDerivativeBound κ V ^ 2) * ‖F‖ ^ 2 / 4 := by
  have hUmem := nativeHalfHighDirichletPhysicalEnergy_memLp hκ0 hκ1 V hV hV0 F
  have hDmem := nativeHalfHighDirichletPhysicalDerivative_memLp hκ0 hκ1 V hV hV0 F
  have hU : IntegrableOn (fun t : ℝ =>
      ‖nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F t‖ ^ 2) (Ici 0) :=
    (memLp_two_iff_integrable_sq_norm hUmem.1).mp hUmem
  have hD : IntegrableOn (fun t : ℝ =>
      ‖nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t‖ ^ 2) (Ici 0) :=
    (memLp_two_iff_integrable_sq_norm hDmem.1).mp hDmem
  refine ⟨hU.add hD, ?_⟩
  rw [integral_add hU hD]
  calc
    _ ≤ nativeHalfHighDirichletEnergyBound κ V ^ 2 * ‖F‖ ^ 2 / 4 +
        nativeHalfHighDirichletDerivativeBound κ V ^ 2 * ‖F‖ ^ 2 / 4 := add_le_add
      (nativeHalfHighDirichletPhysicalEnergy_integral_norm_sq_le hκ0 hκ1 V hV hV0 F)
      (nativeHalfHighDirichletPhysicalDerivative_integral_norm_sq_le hκ0 hκ1 V hV hV0 F)
    _ = _ := by ring

#print axioms halfEnd_memLp_two_and_integral_norm_sq_of_expTwo_bound
#print axioms nativeHalfHighDirichletPhysicalEnergy_memLp
#print axioms nativeHalfHighDirichletPhysicalDerivative_memLp
#print axioms nativeHalfHighDirichletPhysical_total_energy_le

end Yamabe3.Analysis.Delaunay
