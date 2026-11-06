import Yamabe3.Analysis.NativeHalfEndGraphEquation
import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndCompletionAssembly

/-!
# The same H2 graph source, completion and physical model Green identity

The source graph supplies both representatives. No measurable solution or
source representative is an input. One du and one z_E occur before every
completed and smooth test. The physical source retains its factor +8;
its normalized source is F/8 + Q*u. This is not a collar H4 bound and not
a native geometric conormal identification.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff BoundedContinuousFunction RealInnerProductSpace

namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Elliptic
local notation "D" => nativeWeakEuclideanD

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

theorem nativeHalfEndH2Source_completion_and_model_green
    (hVs : ContDiff ℝ ∞ (fun t : ℝ => V t)) (f : HalfEndHighH2Source) :
    let u := cylinderLift (nativeHalfEndH2SourceJoint hκ0 hκ1 V hV hV0 f)
    let F := halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f.1)
    let g := fun x => F x / 8 + nativeHalfEndPotentialCoefficient V x * u x
    let O := Metric.ball (0 : E) 1 \ {(0 : E)}
    MemH01 u O ∧ MemWkpLocally 4 u O ∧ MemLp g 2 (volume.restrict O) ∧
    ∃ du : Fin 3 → Lp ℝ 2 (volume.restrict O), ∃ z_E : H1Zero D O,
      (∀ j, HasWeakPartialDeriv j (du j) u O) ∧
      (toL2 D O z_E : E → ℝ) =ᵐ[volume] O.indicator u ∧
      (toL2 D O z_E : E → ℝ) =ᵐ[volume.restrict O] u ∧
      (∀ η : H1Zero D O,
        IntegrableOn (fun x => g x * (toL2 D O η : E → ℝ) x) O ∧
        gradientEnergy D O z_E η = ∫ x in O, g x * (toL2 D O η : E → ℝ) x) ∧
      gradientEnergy D O z_E z_E = ∫ x in O, ∑ j : Fin 3, du j x ^ 2 ∧
      gradientEnergy D O z_E z_E = ∫ x in O, g x * u x ∧
      ‖z_E‖ ^ 2 = ∫ x in O, u x ^ 2 + (∑ j : Fin 3, du j x ^ 2) ∧
      ‖z_E‖ ^ 2 ≤
        ((2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) ^ 2 / 6 +
          (nativeHalfHighDirichletEnergyBound κ V ^ 2 +
            nativeHalfHighDirichletDerivativeBound κ V ^ 2) / 2) *
          ‖halfEndH2SourceToAngularCLM f.1‖ ^ 2 ∧
      (∀ (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (0 : E) ∉ tsupport φ →
        IntegrableOn (fun x : E => (toL2 D O z_E : E → ℝ) x *
          (-8 * euclideanD.laplacian φ x - 8 * nativeHalfEndPotentialCoefficient V x * φ x)) O ∧
        IntegrableOn (fun x : E => F x * φ x) O ∧
        (∫ x in O, (toL2 D O z_E : E → ℝ) x *
          (-8 * euclideanD.laplacian φ x - 8 * nativeHalfEndPotentialCoefficient V x * φ x)) =
        (∫ x in O, F x * φ x) +
          ∫ θ : S, φ (θ : E) *
            (((-8 : ℝ) • nativeHalfHighDirichletEntranceDerivativeCLM
              hκ0 hκ1 V hV hV0 (halfEndH2SourceToAngularCLM f.1) : AngularL2) : S → ℝ) θ
              ∂angularVolume) := by
  let w := nativeHalfEndH2SourceJoint hκ0 hκ1 V hV hV0 f
  let q := halfEndSourceCylinderCLM (halfEndPhysicalH2SourceGraphValue f.1)
  let u := cylinderLift w
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  let F := halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f.1)
  let Fold := physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) * q p)
  let gold := fun x => Fold x / 8 + nativeHalfEndPotentialCoefficient V x * u x
  let g := fun x => F x / 8 + nativeHalfEndPotentialCoefficient V x * u x
  have hO : IsOpen O := Metric.isOpen_ball.sdiff isClosed_singleton
  have hw : Measurable w := nativeHalfHighDirichletJoint_measurable hκ0 hκ1 V hV hV0 _
  obtain ⟨hu, hg, -, -, du, z_E, hdu, hrep, hrepO, -, hall, -, -, -, hgrad,
      hself, -, -, -, hnorm, hbound, hgreen⟩ :=
    native_forced_halfEnd_completion_variational_green hκ0 hκ1 V hV hV0
      (halfEndH2SourceToAngularCLM f.1) hw q.continuous.measurable
      (nativeHalfHighDirichletJoint_ae hκ0 hκ1 V hV hV0 _)
      (halfEndHighH2Source_representative_ae f)
  have hF : Fold =ᵐ[volume.restrict O] F := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    exact halfEndSourceCylinder_physicalForcing _
      (by simpa using hx.2) (le_of_lt (by simpa using hx.1))
  have hgSame : gold =ᵐ[volume.restrict O] g := by
    filter_upwards [hF] with x hx
    change Fold x / 8 + _ = F x / 8 + _
    rw [hx]
  have hp (η : E → ℝ) : (fun x => gold x * η x) =ᵐ[volume.restrict O]
      (fun x => g x * η x) := hgSame.mul (EventuallyEq.refl _ _)
  refine ⟨hu, nativeHalfEndH2SourceJoint_local_H4 hκ0 hκ1 V hV hV0 hVs f,
    (memLp_congr_ae hgSame).mp hg, du, z_E, hdu, hrep, hrepO, ?_, hgrad,
    hself.trans (integral_congr_ae (hp u)), hnorm, hbound, ?_⟩
  · intro η
    exact ⟨(hall η).1.congr (hp _), (hall η).2.trans (integral_congr_ae (hp _))⟩
  · intro φ hφ hc hzero
    obtain ⟨hI, hJ, hEq⟩ := hgreen φ hφ hc hzero
    have he : (fun x => Fold x * φ x) =ᵐ[volume.restrict O] (fun x => F x * φ x) :=
      hF.mul (EventuallyEq.refl _ _)
    exact ⟨hI, hJ.congr he, hEq.trans (congrArg (fun a : ℝ => a + _)
      (integral_congr_ae he))⟩

#print axioms nativeHalfEndH2Source_completion_and_model_green
end Yamabe3.Analysis.UniformElliptic
