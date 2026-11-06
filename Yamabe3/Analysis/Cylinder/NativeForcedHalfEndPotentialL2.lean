import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndPhysicalL2
import Yamabe3.Analysis.Cylinder.NativeHalfEndCompactTesting

/-!
# The actual singular potential product is globally L2

The coefficient is the original `V(-log |x|) / |x|^2`, and the physical
function is the original `cylinderLift w`.  Their pointwise product is
exactly the lift of `exp(2t) * V(t) * w(t,theta)`, including the retained
zero extension at the origin.

The corresponding actual angular curve is `exp(2t) * V(t)` times the
original constructed Dirichlet curve.  Its bound is `norm V * C0 * norm F`.
The original logarithmic polar integral leaves the weight `exp(-2t)`;
its integral is `1/2`.  This proves the claimed global L2 estimate for
the literal potential product, without assuming global H1 or a bound
for the singular coefficient itself.

Finally the original physical forcing, still divided by eight, is
added to this same potential product.  The true sum is globally L2,
with square integral at most `(1 + norm V^2 * C0^2) * norm F^2`.
No replacement physical solution or replacement source is introduced.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay

/-- The literal singular coefficient times the original lift is the
lift of the same joint representative with its exact inverse-square
time weight.  The identity also holds at the retained zero extension. -/
theorem nativeHalfEndPotentialCoefficient_mul_cylinderLift
    (V : ℝ →ᵇ ℝ) (w : ℝ × S → ℝ) (x : E) :
    nativeHalfEndPotentialCoefficient V x * cylinderLift w x =
      cylinderLift (fun p : ℝ × S => Real.exp (2 * p.1) * V p.1 * w p) x := by
  by_cases hx : x = 0
  · subst x
    simp only [cylinderLift_zero, mul_zero]
  · let y : puncturedSpace := ⟨x, by change x ≠ 0; exact hx⟩
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have he : Real.exp (2 * (-Real.log ‖x‖)) = (‖x‖ ^ 2)⁻¹ := by
      rw [show 2 * (-Real.log ‖x‖) = -(Real.log ‖x‖ + Real.log ‖x‖) by ring,
        Real.exp_neg, Real.exp_add, Real.exp_log hr, pow_two]
    change nativeHalfEndPotentialCoefficient V (y : E) * cylinderLift w (y : E) =
      cylinderLift (fun p : ℝ × S => Real.exp (2 * p.1) * V p.1 * w p) (y : E)
    rw [cylinderLift_coe, cylinderLift_coe]
    change (V (-Real.log ‖x‖) / ‖x‖ ^ 2) *
        (radialScale ‖x‖ * w (-Real.log ‖x‖, sphereDirection y)) =
      radialScale ‖x‖ * (Real.exp (2 * (-Real.log ‖x‖)) *
        V (-Real.log ‖x‖) * w (-Real.log ‖x‖, sphereDirection y))
    rw [he, div_eq_mul_inv]
    ring

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The same original physical function has an actual globally L2
potential product.  Its sharp exponential-integral factor is `1/2`;
the singular coefficient is never assumed globally bounded. -/
theorem native_forced_halfEnd_potential_product_global_memLp
    (F : ℝ≥0 →ᵇ AngularL2) {w : ℝ × S → ℝ} (hw : Measurable w)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ)) :
    MemLp (fun x : E => nativeHalfEndPotentialCoefficient V x * cylinderLift w x) 2
      (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})) ∧
      (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)},
        (nativeHalfEndPotentialCoefficient V x * cylinderLift w x) ^ 2) ≤
        ‖V‖ ^ 2 * (2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) ^ 2 * ‖F‖ ^ 2 / 2 := by
  let U := nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F
  let a : ℝ → ℝ := fun t => Real.exp (2 * t) * V t
  let H : ℝ → AngularL2 := fun t => a t • U t
  let zQ : ℝ × S → ℝ := fun p => a p.1 * w p
  let C : ℝ := (2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) * ‖F‖
  let B : ℝ := ‖V‖ * C
  have hU : Continuous U := nativeHalfHighDirichletPhysical_continuous hκ0 hκ1 V hV hV0 F
  have ha : Continuous a :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (2 * t))).mul V.continuous
  have hH : Continuous H := ha.smul hU
  have hzQ : Measurable zQ := (ha.measurable.comp measurable_fst).mul hw
  have hAE (t : ℝ) : (fun θ => zQ (t, θ)) =ᵐ[angularVolume] (H t : S → ℝ) := by
    have hsmul := (ae_restrict_iff' MeasurableSet.univ).mp (Lp.coeFn_smul (a t) (U t))
    filter_upwards [hwAE t, hsmul] with θ hθ hs
    change a t * w (t, θ) = ((a t • U t : AngularL2) : S → ℝ) θ
    rw [hθ]
    simpa only [Pi.smul_apply, smul_eq_mul] using (hs (mem_univ θ)).symm
  have hUb (t : ℝ) : ‖U t‖ ≤ Real.exp (-2 * t) * C :=
    nativeHalfHighDirichletPhysical_norm_le hκ0 hκ1 V hV hV0 F t
  have hbound (t : ℝ) : ‖H t‖ ≤ B := by
    calc
      _ = Real.exp (2 * t) * ‖V t‖ * ‖U t‖ := by
        dsimp only [H, a]
        rw [norm_smul, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
      _ ≤ Real.exp (2 * t) * ‖V‖ * (Real.exp (-2 * t) * C) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left (V.norm_coe_le_norm t) (Real.exp_pos _).le)
          (hUb t) (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg V))
      _ = (Real.exp (2 * t) * Real.exp (-2 * t)) * (‖V‖ * C) := by ring
      _ = B := by
        rw [← Real.exp_add, show 2 * t + -2 * t = 0 by ring, Real.exp_zero, one_mul]
  have hmajor : IntegrableOn (fun t : ℝ => B ^ 2 * Real.exp (-2 * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0).const_mul (B ^ 2)
  have hpoint (t : ℝ) :
      Real.exp (-2 * t) * ‖H t‖ ^ 2 ≤ B ^ 2 * Real.exp (-2 * t) :=
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hbound t) 2) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  have htime : IntegrableOn (fun t => Real.exp (-2 * t) * ‖H t‖ ^ 2) (Ioi 0) := by
    apply hmajor.mono'
      (((show Continuous (fun t : ℝ => Real.exp (-2 * t)) by fun_prop).mul
        (hH.norm.pow 2)).aestronglyMeasurable.restrict)
    filter_upwards [] with t
    change ‖Real.exp (-2 * t) * ‖H t‖ ^ 2‖ ≤ B ^ 2 * Real.exp (-2 * t)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    exact hpoint t
  have htimeBound : (∫ t in Ioi (0 : ℝ), Real.exp (-2 * t) * ‖H t‖ ^ 2) ≤ B ^ 2 / 2 := by
    calc
      _ ≤ ∫ t in Ioi (0 : ℝ), B ^ 2 * Real.exp (-2 * t) :=
        setIntegral_mono_on htime hmajor measurableSet_Ioi (fun t _ht => hpoint t)
      _ = _ := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0]
        norm_num <;> ring
  obtain ⟨hlift, he⟩ := native_halfEnd_lift_memLp_of_weighted_integrable hzQ hAE htime
  have hproduct : (fun x : E => nativeHalfEndPotentialCoefficient V x * cylinderLift w x) =
      cylinderLift zQ := funext (nativeHalfEndPotentialCoefficient_mul_cylinderLift V w)
  refine ⟨?_, ?_⟩
  · rw [hproduct]
    exact hlift
  · calc
      _ = ∫ x in Metric.ball (0 : E) 1 \ {(0 : E)}, cylinderLift zQ x ^ 2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => congrArg (fun q : ℝ => q ^ 2) (congrFun hproduct x)
      _ = ∫ t in Ioi (0 : ℝ), Real.exp (-2 * t) * ‖H t‖ ^ 2 := he
      _ ≤ B ^ 2 / 2 := htimeBound
      _ = _ := by dsimp only [B, C]; ring

/-- The literal normalized forcing `f/8 + Q*u` of the original global
weak equation is globally L2.  Its square integral is estimated only
after both genuine summands and their sum are proved integrable. -/
theorem native_forced_halfEnd_normalized_rhs_global_memLp
    (F : ℝ≥0 →ᵇ AngularL2) {w z : ℝ × S → ℝ}
    (hw : Measurable w) (hz : Measurable z)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ))
    (hzAE : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume]
      (nativeHighProjection (F t.toNNReal) : S → ℝ)) :
    let u := cylinderLift w
    let f := physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) * z p)
    let O := Metric.ball (0 : E) 1 \ {(0 : E)}
    MemLp (fun x : E => f x / 8 + nativeHalfEndPotentialCoefficient V x * u x) 2
      (volume.restrict O) ∧
    IntegrableOn (fun x : E => (f x / 8 + nativeHalfEndPotentialCoefficient V x * u x) ^ 2) O ∧
    (∫ x in O, (f x / 8 + nativeHalfEndPotentialCoefficient V x * u x) ^ 2) ≤
      (1 + ‖V‖ ^ 2 * (2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) ^ 2) * ‖F‖ ^ 2 := by
  let u := cylinderLift w
  let f := physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) * z p)
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  have hpotential := native_forced_halfEnd_potential_product_global_memLp
    hκ0 hκ1 V hV hV0 F hw hwAE
  have hsource := native_forced_halfEnd_source_global_memLp F hz hzAE
  have hP : MemLp (fun x : E => nativeHalfEndPotentialCoefficient V x * u x) 2
      (volume.restrict O) := hpotential.1
  have hN : MemLp (fun x : E => f x / 8) 2 (volume.restrict O) := by
    simpa only [div_eq_mul_inv] using hsource.1.mul_const (8 : ℝ)⁻¹
  have hR : MemLp (fun x : E => f x / 8 + nativeHalfEndPotentialCoefficient V x * u x) 2
      (volume.restrict O) := by
    exact hN.add hP
  have hNI : IntegrableOn (fun x : E => (f x / 8) ^ 2) O := hN.integrable_sq
  have hPI : IntegrableOn (fun x : E => (nativeHalfEndPotentialCoefficient V x * u x) ^ 2) O :=
    hP.integrable_sq
  have hRI : IntegrableOn (fun x : E =>
      (f x / 8 + nativeHalfEndPotentialCoefficient V x * u x) ^ 2) O := hR.integrable_sq
  have hNbound : (∫ x in O, (f x / 8) ^ 2) ≤ ‖F‖ ^ 2 / 2 := by
    calc
      _ = (1 / 64 : ℝ) * ∫ x in O, f x ^ 2 := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ ≤ (1 / 64 : ℝ) * (32 * ‖F‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsource.2 (by norm_num : (0 : ℝ) ≤ 1 / 64)
      _ = _ := by ring
  refine ⟨hR, hRI, ?_⟩
  calc
    _ ≤ ∫ x in O, 2 * ((f x / 8) ^ 2 +
        (nativeHalfEndPotentialCoefficient V x * u x) ^ 2) := by
      apply integral_mono_ae hRI ((hNI.add hPI).const_mul 2)
      exact Eventually.of_forall fun x => add_sq_le
    _ = 2 * ((∫ x in O, (f x / 8) ^ 2) +
        ∫ x in O, (nativeHalfEndPotentialCoefficient V x * u x) ^ 2) := by
      rw [integral_const_mul, integral_add hNI hPI]
    _ ≤ 2 * (‖F‖ ^ 2 / 2 +
        ‖V‖ ^ 2 * (2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) ^ 2 * ‖F‖ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hNbound hpotential.2) (by norm_num : (0 : ℝ) ≤ 2)
    _ = _ := by ring

#print axioms nativeHalfEndPotentialCoefficient_mul_cylinderLift
#print axioms native_forced_halfEnd_potential_product_global_memLp
#print axioms native_forced_halfEnd_normalized_rhs_global_memLp

end Yamabe3.Analysis.SpherePolar
