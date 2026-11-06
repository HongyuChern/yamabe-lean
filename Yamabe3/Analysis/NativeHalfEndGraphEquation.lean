import Yamabe3.Analysis.NativeHalfEndH2SourceSolver
import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndVariational

/-!
# The literal source graph and the same zero-entrance solution in the weak equation

All source conversions are proved on the physical punctured unit ball.
One `du` and the one previously selected `u` work for all Sobolev tests
and for self-testing.  No extra weak-equation or regularity premise is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff BoundedContinuousFunction RealInnerProductSpace

namespace Yamabe3.Analysis.UniformElliptic

open Delaunay SpherePolar SphereSpectrum
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Elliptic

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

theorem nativeHalfEndH2Source_same_variational_equation
    (hVs : ContDiff ℝ ∞ (fun t : ℝ => V t)) (f : HalfEndHighH2Source) :
    let u := cylinderLift (nativeHalfEndH2SourceJoint hκ0 hκ1 V hV hV0 f)
    let F := halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f.1)
    let g := fun x => F x / 8 + nativeHalfEndPotentialCoefficient V x * u x
    let O := Metric.ball (0 : E) 1 \ {(0 : E)}
    MemH01 u O ∧ MemWkpLocally 4 u O ∧ MemLp g 2 (volume.restrict O) ∧
    ∃ du : Fin 3 → Lp ℝ 2 (volume.restrict O),
      (∀ j, HasWeakPartialDeriv j (du j) u O) ∧
      (∀ (η : E → ℝ), MemH01 η O → ∀ (p : Fin 3 → E → ℝ),
        (∀ j, MemLp (p j) 2 (volume.restrict O)) →
        (∀ j, HasWeakPartialDeriv j (p j) η O) →
        IntegrableOn (fun x => ∑ j : Fin 3, du j x * p j x) O ∧
        IntegrableOn (fun x => g x * η x) O ∧
        (∫ x in O, ∑ j : Fin 3, du j x * p j x) = ∫ x in O, g x * η x) ∧
      IntegrableOn (fun x => ∑ j : Fin 3, du j x ^ 2) O ∧
      IntegrableOn (fun x => g x * u x) O ∧
      (∫ x in O, ∑ j : Fin 3, du j x ^ 2) = ∫ x in O, g x * u x := by
  let w := nativeHalfEndH2SourceJoint hκ0 hκ1 V hV hV0 f
  let z := halfEndSourceCylinderCLM (halfEndPhysicalH2SourceGraphValue f.1)
  let u := cylinderLift w
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  let F := halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f.1)
  let fOld := physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) * z p)
  let gOld := fun x => fOld x / 8 + nativeHalfEndPotentialCoefficient V x * u x
  let g := fun x => F x / 8 + nativeHalfEndPotentialCoefficient V x * u x
  have hO : IsOpen O := Metric.isOpen_ball.sdiff isClosed_singleton
  have hw : Measurable w := nativeHalfHighDirichletJoint_measurable hκ0 hκ1 V hV hV0 _
  have hz : Measurable (fun p => z p) := z.continuous.measurable
  obtain ⟨hu0, hg, -, -, du, hdu, hvar, hgradI, hgU, henergy, -, -, -⟩ :=
    native_forced_halfEnd_global_variational_equation hκ0 hκ1 V hV hV0
      (halfEndH2SourceToAngularCLM f.1) hw hz
      (nativeHalfHighDirichletJoint_ae hκ0 hκ1 V hV hV0 _)
      (halfEndHighH2Source_representative_ae f)
  have hsame : gOld =ᵐ[volume.restrict O] g := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    have hf : fOld x = F x := halfEndSourceCylinder_physicalForcing _
      (by simpa using hx.2) (le_of_lt (by simpa using hx.1))
    change fOld x / 8 + nativeHalfEndPotentialCoefficient V x * u x =
      F x / 8 + nativeHalfEndPotentialCoefficient V x * u x
    rw [hf]
  have hpair (η : E → ℝ) : (fun x => gOld x * η x) =ᵐ[volume.restrict O]
      (fun x => g x * η x) := hsame.mul (EventuallyEq.refl _ _)
  refine ⟨hu0, nativeHalfEndH2SourceJoint_local_H4 hκ0 hκ1 V hV hV0 hVs f,
    (memLp_congr_ae hsame).mp hg, du, hdu, ?_, hgradI, hgU.congr (hpair u), ?_⟩
  · intro η hη p hp hweak
    obtain ⟨hI, hJ, hEq⟩ := hvar η hη p hp hweak
    exact ⟨hI, hJ.congr (hpair η), hEq.trans (integral_congr_ae (hpair η))⟩
  · exact henergy.trans (integral_congr_ae (hpair u))

#print axioms nativeHalfEndH2Source_same_variational_equation

end Yamabe3.Analysis.UniformElliptic
