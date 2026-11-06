import Yamabe3.Analysis.Cylinder.NativeProjectedC2PhysicalEquation
import Yamabe3.Analysis.Cylinder.NativeContinuousAngularApproximation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Actual L2 forcing for the original continuous angular source

The physical source is the existing `physicalForcing` applied to the
literal exp(-2t) weight. Its proved value is -8 times the original lift.
Thus finite source errors have exactly 64 times the original lift square
error, on the same shell and along the same finite spectral exhaustion.

The global punctured-unit-ball result is proved separately from the
actual logarithmic polar integral. Its original Hilbert source bound
gives an exp(-2t) integrable majorant on positive time. The resulting
physical source square integral is at most 32 B^2. No global physical L2
bound, global gradient bound, or smooth-source hypothesis is assumed.
This module is newly proved source, not a recovered historical payload.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay

/-- The source error has its literal coefficient-eight square factor.
This algebraic identity is valid for every measure; L2 membership is
established in the following production lemmas. -/
theorem integral_physicalForcing_expNegTwo_sq_sub
    (μ : Measure E) (z w : ℝ × S → ℝ) :
    (∫ x, (physicalForcing (fun p => Real.exp (-2 * p.1) * z p) x -
      physicalForcing (fun p => Real.exp (-2 * p.1) * w p) x) ^ 2 ∂μ) =
      64 * ∫ x, (cylinderLift z x - cylinderLift w x) ^ 2 ∂μ := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [physicalForcing_expNegTwo, physicalForcing_expNegTwo]
    ring

theorem memLp_projected_halfEnd_physicalForcing_on_shell
    (s : Finset AngularIndex) {U : ℝ → AngularL2} (hU : Continuous U) (a b : ℝ) :
    MemLp (physicalForcing (fun p =>
      Real.exp (-2 * p.1) * projectedAngular s U p)) 2
      (volume.restrict (cylinderShell a b)) := by
  rw [show physicalForcing (fun p => Real.exp (-2 * p.1) * projectedAngular s U p) =
      (fun x => -8 * cylinderLift (projectedAngular s U) x) from
    funext (physicalForcing_expNegTwo (projectedAngular s U))]
  exact (memLp_projectedAngular_lift_of_continuous s hU a b).const_mul (-8)

theorem memLp_halfEnd_physicalForcing_on_shell
    {U : ℝ → AngularL2} (hU : Continuous U)
    {z : ℝ × S → ℝ} (hz : Measurable z)
    (hae : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ)) (a b : ℝ) :
    MemLp (physicalForcing (fun p => Real.exp (-2 * p.1) * z p)) 2
      (volume.restrict (cylinderShell a b)) := by
  rw [show physicalForcing (fun p => Real.exp (-2 * p.1) * z p) =
      (fun x => -8 * cylinderLift z x) from funext (physicalForcing_expNegTwo z)]
  exact (memLp_continuous_angular_lift hU hz hae a b).const_mul (-8)

/-- Strong L2 convergence of the actual physical sources on a fixed
shell follows from the original continuous Hilbert projection errors. -/
theorem integral_projected_halfEnd_physicalForcing_error_tendsto
    {s : ℕ → Finset AngularIndex} (hs : Tendsto s atTop atTop)
    {U : ℝ → AngularL2} (hU : Continuous U)
    {z : ℝ × S → ℝ} (hz : Measurable z)
    (hae : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ)) (a b : ℝ) :
    Tendsto (fun n => ∫ x in cylinderShell a b,
      (physicalForcing (fun p => Real.exp (-2 * p.1) * projectedAngular (s n) U p) x -
        physicalForcing (fun p => Real.exp (-2 * p.1) * z p) x) ^ 2) atTop (𝓝 0) := by
  have h := (integral_projectedAngular_lift_error_tendsto_of_continuous
    hs hU hz hae a b).const_mul (64 : ℝ)
  simpa only [integral_physicalForcing_expNegTwo_sq_sub, mul_zero] using h

private theorem cylinderPoint_mem_forcing_halfEnd_iff (p : ℝ × S) :
    cylinderPoint p ∈ Metric.ball (0 : E) 1 \ {(0 : E)} ↔ 0 < p.1 := by
  simp only [mem_diff, Metric.mem_ball, dist_zero_right, cylinderPoint_norm,
    mem_singleton_iff, cylinderPoint_ne_zero p, not_false_eq_true, and_true]
  rw [← Real.exp_zero, Real.exp_lt_exp]
  exact neg_lt_zero

private theorem logCylinderWeight_forcing_halfEnd_square (z : ℝ × S → ℝ) :
    logCylinderWeight ((Metric.ball (0 : E) 1 \ {(0 : E)}).indicator
      (fun x : E => cylinderLift z x ^ 2)) =
      (Ioi (0 : ℝ) ×ˢ (univ : Set S)).indicator
        (fun p : ℝ × S => Real.exp (-2 * p.1) * z p ^ 2) := by
  funext p
  have hp := cylinderPoint_mem_forcing_halfEnd_iff p
  by_cases ht : 0 < p.1
  · have hx := hp.mpr ht
    change Real.exp (-3 * p.1) * (Metric.ball (0 : E) 1 \ {(0 : E)}).indicator
      (fun x : E => cylinderLift z x ^ 2) (cylinderPoint p) = _
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem
      (show p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set S) from ⟨ht, mem_univ _⟩)]
    change Real.exp (-3 * p.1) * cylinderLift z (Real.exp (-p.1) • (p.2 : E)) ^ 2 = _
    rw [cylinderLift_smul z (Real.exp_pos _) p.2, Real.log_exp, neg_neg, mul_pow,
      radialScale_exp_neg]
    have he : Real.exp (-3 * p.1) * Real.exp (p.1 / 2) ^ 2 = Real.exp (-2 * p.1) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [← mul_assoc, he]
  · have hx : cylinderPoint p ∉ Metric.ball (0 : E) 1 \ {(0 : E)} :=
      fun hx => ht (hp.mp hx)
    change Real.exp (-3 * p.1) * (Metric.ball (0 : E) 1 \ {(0 : E)}).indicator
      (fun x : E => cylinderLift z x ^ 2) (cylinderPoint p) = _
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem
      (show p ∉ Ioi (0 : ℝ) ×ˢ (univ : Set S) from fun hp => ht hp.1), mul_zero]

/-- The actual positive-time weighted Hilbert square integral is exactly
the original physical lift square integral on the punctured unit ball.
The integrability hypothesis is on the one-dimensional weighted norm,
and will be supplied from the original source bound below. -/
theorem native_halfEnd_lift_memLp_of_weighted_integrable
    {U : ℝ → AngularL2} {z : ℝ × S → ℝ} (hz : Measurable z)
    (hae : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ))
    (htime : IntegrableOn (fun t => Real.exp (-2 * t) * ‖U t‖ ^ 2) (Ioi 0)) :
    MemLp (cylinderLift z) 2
      (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})) ∧
      (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)}, cylinderLift z x ^ 2) =
        ∫ t in Ioi (0 : ℝ), Real.exp (-2 * t) * ‖U t‖ ^ 2 := by
  let g (p : ℝ × S) := Real.exp (-2 * p.1) * z p ^ 2
  have hg : Measurable g := (by fun_prop : Measurable
    (fun p : ℝ × S => Real.exp (-2 * p.1))).mul (hz.pow_const 2)
  have hs (t : ℝ) : MemLp (fun θ => z (t, θ)) 2 angularVolume := by
    have hu : MemLp (U t : S → ℝ) 2 angularVolume := by
      simpa only [Measure.restrict_univ] using Lp.memLp (U t)
    exact (memLp_congr_ae (hae t)).mpr hu
  have hnorm (t : ℝ) : (∫ θ : S, ‖g (t, θ)‖ ∂angularVolume) =
      Real.exp (-2 * t) * ‖U t‖ ^ 2 := by
    calc
      _ = ∫ θ : S, Real.exp (-2 * t) * z (t, θ) ^ 2 ∂angularVolume := by
        apply integral_congr_ae
        exact Eventually.of_forall fun θ => by
          dsimp only [g]
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
      _ = _ := by rw [integral_const_mul, native_joint_integral_sq hae]
  have hprod : Integrable g ((volume.restrict (Ioi (0 : ℝ))).prod angularVolume) := by
    apply (integrable_prod_iff hg.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (fun t => (hs t).integrable_sq.const_mul (Real.exp (-2 * t))), ?_⟩
    simpa only [IntegrableOn, hnorm] using htime
  have hO : MeasurableSet (Metric.ball (0 : E) 1 \ {(0 : E)}) :=
    (Metric.isOpen_ball.sdiff isClosed_singleton).measurableSet
  have hI : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set S)) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  have hmeasure : (volume.restrict (Ioi (0 : ℝ))).prod angularVolume =
      (volume.prod angularVolume).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set S)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hmeasure] at hprod
  have hind : Integrable ((Ioi (0 : ℝ) ×ˢ (univ : Set S)).indicator g)
      (volume.prod angularVolume) := (integrable_indicator_iff hI).mpr hprod
  have hm : Measurable ((Metric.ball (0 : E) 1 \ {(0 : E)}).indicator
      (fun x : E => cylinderLift z x ^ 2)) :=
    ((measurable_cylinderLift hz).pow_const 2).indicator hO
  have hi : Integrable ((Metric.ball (0 : E) 1 \ {(0 : E)}).indicator
      (fun x : E => cylinderLift z x ^ 2)) := by
    apply (integrable_euclidean_iff_cylinder hm).mpr
    rw [logCylinderWeight_forcing_halfEnd_square]
    exact hind
  have hlift : MemLp (cylinderLift z) 2
      (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})) :=
    (memLp_two_iff_integrable_sq (measurable_cylinderLift hz).aestronglyMeasurable).mpr
      ((integrable_indicator_iff hO).mp hi)
  refine ⟨hlift, ?_⟩
  have hinner (t : ℝ) : (∫ θ : S,
      (Ioi (0 : ℝ) ×ˢ (univ : Set S)).indicator g (t, θ) ∂angularVolume) =
      (Ioi (0 : ℝ)).indicator (fun a => Real.exp (-2 * a) * ‖U a‖ ^ 2) t := by
    by_cases ht : 0 < t
    · rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
      calc
        _ = ∫ θ : S, Real.exp (-2 * t) * z (t, θ) ^ 2 ∂angularVolume := by
          apply integral_congr_ae
          exact Eventually.of_forall fun θ => by
            simpa only [g] using Set.indicator_of_mem
              (show (t, θ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set S) from ⟨ht, mem_univ _⟩) g
        _ = _ := by rw [integral_const_mul, native_joint_integral_sq hae]
    · rw [Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
      apply integral_eq_zero_of_ae
      exact Eventually.of_forall fun θ => Set.indicator_of_notMem
        (show (t, θ) ∉ Ioi (0 : ℝ) ×ˢ (univ : Set S) from fun hp => ht hp.1) g
  calc
    _ = ∫ x : E, (Metric.ball (0 : E) 1 \ {(0 : E)}).indicator
        (fun y : E => cylinderLift z y ^ 2) x := (integral_indicator hO).symm
    _ = ∫ t : ℝ, ∫ θ : S, logCylinderWeight
        ((Metric.ball (0 : E) 1 \ {(0 : E)}).indicator
          (fun x : E => cylinderLift z x ^ 2)) (t, θ) ∂angularVolume :=
      integral_euclidean_eq_cylinder hm hi
    _ = ∫ t : ℝ, (Ioi (0 : ℝ)).indicator
        (fun a => Real.exp (-2 * a) * ‖U a‖ ^ 2) t := by
      rw [logCylinderWeight_forcing_halfEnd_square]
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by simpa only [g] using hinner t
    _ = _ := integral_indicator measurableSet_Ioi

/-- The original bounded continuous Hilbert source produces actual L2
physical forcing on the whole punctured unit ball, with its proved
coefficient-eight bound 32 B^2. -/
theorem native_halfEnd_physicalForcing_memLp
    {U : ℝ → AngularL2} (hU : Continuous U)
    {z : ℝ × S → ℝ} (hz : Measurable z)
    (hae : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ))
    {B : ℝ} (hbound : ∀ t, 0 ≤ t → ‖U t‖ ≤ B) :
    MemLp (physicalForcing (fun p => Real.exp (-2 * p.1) * z p)) 2
      (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})) ∧
      (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)},
        physicalForcing (fun p => Real.exp (-2 * p.1) * z p) x ^ 2) ≤ 32 * B ^ 2 := by
  have hmajorant : IntegrableOn (fun t : ℝ => B ^ 2 * Real.exp (-2 * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0).const_mul (B ^ 2)
  have hle (t : ℝ) (ht : 0 < t) :
      Real.exp (-2 * t) * ‖U t‖ ^ 2 ≤ B ^ 2 * Real.exp (-2 * t) := by
    exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hbound t ht.le) 2) (Real.exp_pos _).le).trans_eq
        (mul_comm _ _)
  have htime : IntegrableOn (fun t => Real.exp (-2 * t) * ‖U t‖ ^ 2) (Ioi 0) := by
    apply hmajorant.mono'
      (((show Continuous (fun t : ℝ => Real.exp (-2 * t)) by fun_prop).mul
        (hU.norm.pow 2)).aestronglyMeasurable.restrict)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖Real.exp (-2 * t) * ‖U t‖ ^ 2‖ ≤ B ^ 2 * Real.exp (-2 * t)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    exact hle t ht
  have htimeBound : (∫ t in Ioi (0 : ℝ), Real.exp (-2 * t) * ‖U t‖ ^ 2) ≤ B ^ 2 / 2 := by
    calc
      _ ≤ ∫ t in Ioi (0 : ℝ), B ^ 2 * Real.exp (-2 * t) :=
        setIntegral_mono_on htime hmajorant measurableSet_Ioi (fun t ht => hle t ht)
      _ = _ := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0)]
        norm_num <;> ring
  obtain ⟨hlift, he⟩ := native_halfEnd_lift_memLp_of_weighted_integrable hz hae htime
  refine ⟨?_, ?_⟩
  · rw [show physicalForcing (fun p => Real.exp (-2 * p.1) * z p) =
        (fun x => -8 * cylinderLift z x) from funext (physicalForcing_expNegTwo z)]
    exact hlift.const_mul (-8)
  · calc
      _ = 64 * ∫ x in Metric.ball (0 : E) 1 \ {(0 : E)}, cylinderLift z x ^ 2 := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp only
          rw [physicalForcing_expNegTwo]
          ring
      _ = 64 * ∫ t in Ioi (0 : ℝ), Real.exp (-2 * t) * ‖U t‖ ^ 2 := by rw [he]
      _ ≤ 64 * (B ^ 2 / 2) := mul_le_mul_of_nonneg_left htimeBound (by norm_num)
      _ = 32 * B ^ 2 := by ring

#print axioms integral_physicalForcing_expNegTwo_sq_sub
#print axioms memLp_projected_halfEnd_physicalForcing_on_shell
#print axioms memLp_halfEnd_physicalForcing_on_shell
#print axioms integral_projected_halfEnd_physicalForcing_error_tendsto
#print axioms native_halfEnd_lift_memLp_of_weighted_integrable
#print axioms native_halfEnd_physicalForcing_memLp

end Yamabe3.Analysis.SpherePolar
