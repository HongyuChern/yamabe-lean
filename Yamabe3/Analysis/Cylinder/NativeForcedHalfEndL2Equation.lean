import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndQuantitativeH1
import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndPotentialL2

/-!
# The same quantitative global H1 solution has a genuine L2 right-hand side

The quantitative global equation selects its actual weak gradient once.
The separately produced potential-product estimate applies to that same
original physical value and source.  The normalized right-hand side is
literally `f/8 + Q*u`, with the original physical forcing and potential.

The compact-test pairings are genuinely integrable before they are
combined into one integral.  All original finite-set strong convergence,
gradient-energy convergence and quantitative H1 bounds are retained for
the same weak gradient.  No regularity or equation is supplied as an input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The same original representative, source and produced weak gradient
satisfy one genuine global L2 forcing equation, together with full
finite-set strong convergence and all quantitative square-energy bounds. -/
theorem native_forced_halfEnd_global_quantitative_L2_equation
    (F : ℝ≥0 →ᵇ AngularL2) {w z : ℝ × S → ℝ}
    (hw : Measurable w) (hz : Measurable z)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ))
    (hzAE : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume]
      (nativeHighProjection (F t.toNNReal) : S → ℝ)) :
    let u := cylinderLift w
    let f := physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) * z p)
    let g := fun x : E => f x / 8 + nativeHalfEndPotentialCoefficient V x * u x
    let uFin := fun s : Finset AngularIndex => cylinderLift (projectedAngular s
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F))
    let O := Metric.ball (0 : E) 1 \ {(0 : E)}
    Poincare.Analysis.Sobolev.Weak.MemH1 u O ∧
    MemLp g 2 (volume.restrict O) ∧
    IntegrableOn (fun x : E => g x ^ 2) O ∧
    (∫ x in O, g x ^ 2) ≤
      (1 + ‖V‖ ^ 2 * (2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) ^ 2) * ‖F‖ ^ 2 ∧
    ∃ du : Fin 3 → Lp ℝ 2 (volume.restrict O),
      (∀ j, Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv j (du j) u O) ∧
      Tendsto (fun s : Finset AngularIndex => ∫ x in O,
        ((uFin s x - u x) ^ 2 + (∑ j : Fin 3,
          (fderiv ℝ (uFin s) x (EuclideanSpace.single j 1) - du j x) ^ 2)))
        atTop (𝓝 0) ∧
      Tendsto (fun s : Finset AngularIndex => ∫ x in O, ∑ j : Fin 3,
        (fderiv ℝ (uFin s) x (EuclideanSpace.single j 1)) ^ 2)
        atTop (𝓝 (∫ x in O, ∑ j : Fin 3, du j x ^ 2)) ∧
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
        (∫ x in O, ∑ j : Fin 3, du j x * fderiv ℝ φ x (EuclideanSpace.single j 1)) =
          ∫ x in O, g x * φ x) ∧
      IntegrableOn (fun x : E => ∑ j : Fin 3, du j x ^ 2) O ∧
      (∫ x in O, ∑ j : Fin 3, du j x ^ 2) ≤
        (nativeHalfHighDirichletEnergyBound κ V ^ 2 +
          nativeHalfHighDirichletDerivativeBound κ V ^ 2) * ‖F‖ ^ 2 / 2 ∧
      IntegrableOn (fun x : E => (u x ^ 2 + (∑ j : Fin 3, du j x ^ 2))) O ∧
      (∫ x in O, (u x ^ 2 + (∑ j : Fin 3, du j x ^ 2))) ≤
        ((2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) ^ 2 / 6 +
          (nativeHalfHighDirichletEnergyBound κ V ^ 2 +
            nativeHalfHighDirichletDerivativeBound κ V ^ 2) / 2) * ‖F‖ ^ 2 := by
  let u := cylinderLift w
  let f := physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) * z p)
  let g := fun x : E => f x / 8 + nativeHalfEndPotentialCoefficient V x * u x
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  obtain ⟨hH1, du, hdu, hstrong, henergy, heq, hgradI, hgradBound, htotalI, htotalBound⟩ :=
    native_forced_halfEnd_global_quantitative_strong_equation hκ0 hκ1 V hV hV0 F hw hz hwAE hzAE
  obtain ⟨hR, hRI, hRBound⟩ :=
    native_forced_halfEnd_normalized_rhs_global_memLp hκ0 hκ1 V hV hV0 F hw hz hwAE hzAE
  refine ⟨hH1, hR, hRI, hRBound, du, hdu, hstrong, henergy, ?_,
    hgradI, hgradBound, htotalI, htotalBound⟩
  intro φ hφ hc hs
  have hφLp : MemLp φ 2 (volume.restrict O) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).restrict O
  have hfLp : MemLp f 2 (volume.restrict O) :=
    (native_forced_halfEnd_source_global_memLp F hz hzAE).1
  have hpLp : MemLp (fun x : E => nativeHalfEndPotentialCoefficient V x * u x) 2
      (volume.restrict O) :=
    (native_forced_halfEnd_potential_product_global_memLp hκ0 hκ1 V hV hV0 F hw hwAE).1
  have hsrc : Integrable (fun x : E => f x * φ x) (volume.restrict O) :=
    hfLp.integrable_mul hφLp
  have hpot : Integrable (fun x : E =>
      (nativeHalfEndPotentialCoefficient V x * u x) * φ x) (volume.restrict O) :=
    hpLp.integrable_mul hφLp
  calc
    _ = (∫ x in O, f x * φ x) / 8 +
        ∫ x in O, u x * (nativeHalfEndPotentialCoefficient V x * φ x) := heq φ hφ hc hs
    _ = (∫ x in O, (f x * φ x) / 8) +
        ∫ x in O, (nativeHalfEndPotentialCoefficient V x * u x) * φ x := by
      rw [integral_div]
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = ∫ x in O, ((f x * φ x) / 8 +
        (nativeHalfEndPotentialCoefficient V x * u x) * φ x) :=
      (integral_add (hsrc.div_const 8) hpot).symm
    _ = ∫ x in O, g x * φ x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only [g]; ring

#print axioms native_forced_halfEnd_global_quantitative_L2_equation

end Yamabe3.Analysis.SpherePolar
