import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndL2Equation
import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndZeroBoundary
import PoincareLib.Analysis.Elliptic.Regularity.WeakTestExtension

/-!
# The same forced field satisfies the variational and self-test identities

The quantitative global L2 equation is unpacked exactly once, so every
conclusion below retains its one chosen weak gradient `du`.  The actual
zero-boundary producer supplies `MemH01` of the same original function.
The pinned Sobolev test extension then accepts any actual L2 weak
gradient of an arbitrary `MemH01` test function.  Its internal weak
derivative uniqueness identifies that test gradient with the one in the
test function's approximation witness, without changing the original du.

All variational pairings are proved integrable before their identities
are recorded.  Testing with the original function and that same du gives
the actual total gradient energy identity.  The original normalized
right-hand side `f/8 + Q*u`, its genuine L2 bound, and the quantitative
gradient and H1 bounds are retained.

This candidate depends on the actual zero-boundary producer.  Acceptance
requires successful compilation of that dependency and this leaf;
source assembly alone is not acceptance.  No boundary conormal identity
or boundary Green formula is claimed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- One actual original value, source and weak gradient satisfy the
zero-boundary variational equation for every genuine Sobolev test,
the self-test energy identity, and the original quantitative L2/H1
bounds.  No zero-boundary membership or equation is supplied as input. -/
theorem native_forced_halfEnd_global_variational_equation
    (F : ℝ≥0 →ᵇ AngularL2) {w z : ℝ × S → ℝ}
    (hw : Measurable w) (hz : Measurable z)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ))
    (hzAE : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume]
      (nativeHighProjection (F t.toNNReal) : S → ℝ)) :
    let u := cylinderLift w
    let f := physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) * z p)
    let g := fun x : E => f x / 8 + nativeHalfEndPotentialCoefficient V x * u x
    let O := Metric.ball (0 : E) 1 \ {(0 : E)}
    MemH01 u O ∧
    MemLp g 2 (volume.restrict O) ∧
    IntegrableOn (fun x : E => g x ^ 2) O ∧
    (∫ x in O, g x ^ 2) ≤
      (1 + ‖V‖ ^ 2 * (2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) ^ 2) * ‖F‖ ^ 2 ∧
    ∃ du : Fin 3 → Lp ℝ 2 (volume.restrict O),
      (∀ j, HasWeakPartialDeriv j (du j) u O) ∧
      (∀ (v : E → ℝ), MemH01 v O → ∀ (q : Fin 3 → E → ℝ),
        (∀ j, MemLp (q j) 2 (volume.restrict O)) →
        (∀ j, HasWeakPartialDeriv j (q j) v O) →
        IntegrableOn (fun x : E => ∑ j : Fin 3, du j x * q j x) O ∧
        IntegrableOn (fun x : E => g x * v x) O ∧
        (∫ x in O, ∑ j : Fin 3, du j x * q j x) = ∫ x in O, g x * v x) ∧
      IntegrableOn (fun x : E => ∑ j : Fin 3, du j x ^ 2) O ∧
      IntegrableOn (fun x : E => g x * u x) O ∧
      (∫ x in O, ∑ j : Fin 3, du j x ^ 2) = (∫ x in O, g x * u x) ∧
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
  have hO : IsOpen O := Metric.isOpen_ball.sdiff isClosed_singleton
  obtain ⟨_hH1, hg, hgI, hgBound, du, hdu, _hstrong, _henergy, heq,
      hgradI, hgradBound, htotalI, htotalBound⟩ :=
    native_forced_halfEnd_global_quantitative_L2_equation hκ0 hκ1 V hV hV0 F hw hz hwAE hzAE
  have hu0 : MemH01 u O := native_forced_halfEnd_memH01 hκ0 hκ1 V hV hV0 F hw hwAE
  have hflux (j : Fin 3) : MemLp (fun x : E => du j x) 2 (volume.restrict O) := Lp.memLp (du j)
  have hvar (v : E → ℝ) (hv : MemH01 v O) (q : Fin 3 → E → ℝ)
      (hq : ∀ j, MemLp (q j) 2 (volume.restrict O))
      (hwq : ∀ j, HasWeakPartialDeriv j (q j) v O) :
      IntegrableOn (fun x : E => ∑ j : Fin 3, du j x * q j x) O ∧
      IntegrableOn (fun x : E => g x * v x) O ∧
      (∫ x in O, ∑ j : Fin 3, du j x * q j x) = ∫ x in O, g x * v x := by
    have hvLp : MemLp v 2 (volume.restrict O) := hv.1.1
    refine ⟨integrable_finsetSum Finset.univ (fun j _ => (hflux j).integrable_mul (hq j)),
      hg.integrable_mul hvLp, ?_⟩
    exact Poincare.Analysis.Elliptic.weakEquation_of_memW01p
      (F := fun j x => du j x) (f := g) (v := v) (q := q)
      hO hflux hg heq hv hq hwq
  have hself := hvar u hu0 (fun j x => du j x) hflux hdu
  refine ⟨hu0, hg, hgI, hgBound, du, hdu, hvar, hgradI, hself.2.1, ?_,
    hgradBound, htotalI, htotalBound⟩
  simpa only [pow_two] using hself.2.2

#print axioms native_forced_halfEnd_global_variational_equation

end Yamabe3.Analysis.SpherePolar
