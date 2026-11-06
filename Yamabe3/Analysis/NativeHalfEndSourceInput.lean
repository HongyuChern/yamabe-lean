import Yamabe3.Analysis.UniformElliptic.HalfEndPhysicalH2SourceGraph
import Yamabe3.Analysis.NativeCylinderSourceSpace
import Yamabe3.Analysis.Cylinder.NativeProjectedC2PhysicalEquation

/-!
# The actual physical source graph supplies the native half-line source

This constructs a bounded linear map, not a source-realization assumption.
The negative sign is essential: `physicalForcing` is `-8` times the lifted
cylinder source after the exp(-2t) weight.  Clipping time only totalizes a
continuous source on negative times; no H2 extension claim is made there.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter Metric MeasureTheory PoincareMT
open scoped Topology NNReal BoundedContinuousFunction

namespace Yamabe3.Analysis.UniformElliptic

open Delaunay SpherePolar SphereSpectrum
open Poincare.Geometry.Riemannian.SpaceForm

def halfEndSourceCylinderPoint : C(ℝ × S, HalfEndSourceEntrance) where
  toFun p := ⟨Real.exp (-max p.1 0) • (p.2 : E), by
    have hn : ‖Real.exp (-max p.1 0) • (p.2 : E)‖ = Real.exp (-max p.1 0) := by
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le,
        norm_eq_of_mem_sphere, mul_one]
    constructor
    · intro h
      rw [h, norm_zero] at hn
      exact (Real.exp_pos _).ne' hn.symm
    · rw [hn]
      have he : Real.exp (-max p.1 0) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_right _ _))
      linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((Real.continuous_exp.comp (continuous_fst.max continuous_const).neg).smul
      (continuous_subtype_val.comp continuous_snd))

/-- A fixed continuous totalization of the signed physical source data. -/
def halfEndSourceCylinderCLM : HalfEndSourceValue →L[ℝ] CylinderSource :=
  -(BoundedContinuousFunction.compContinuousCLM ℝ ℝ halfEndSourceCylinderPoint)

theorem halfEndSourceCylinderCLM_norm_le (f : HalfEndSourceValue) :
    ‖halfEndSourceCylinderCLM f‖ ≤ ‖f‖ := by
  change ‖-(f.compContinuous halfEndSourceCylinderPoint)‖ ≤ ‖f‖
  rw [norm_neg]
  exact BoundedContinuousFunction.norm_compContinuous_le _ _

theorem halfEndSourceCylinderCLM_apply_nonneg (f : HalfEndSourceValue)
    {t : ℝ} (ht : 0 ≤ t) (θ : S) :
    halfEndSourceCylinderCLM f (t, θ) =
      -halfEndSourceExtension f (Real.exp (-t) • (θ : E)) := by
  have hp := (halfEndSourceCylinderPoint (t, θ)).property
  change -f (halfEndSourceCylinderPoint (t, θ)) = _
  have hmax : max t 0 = t := max_eq_left ht
  simp only [halfEndSourceCylinderPoint, ContinuousMap.coe_mk, hmax] at hp ⊢
  rw [halfEndSourceExtension_of_mem f hp]

def halfEndSourceToAngularCLM : HalfEndSourceValue →L[ℝ] (ℝ≥0 →ᵇ AngularL2) :=
  (BoundedContinuousFunction.compContinuousCLM AngularL2 ℝ
    ⟨fun t : ℝ≥0 => (t : ℝ), continuous_subtype_val⟩).comp
      (cylinderToAngularL2CLM.comp halfEndSourceCylinderCLM)

theorem halfEndSourceToAngularCLM_apply (f : HalfEndSourceValue) (t : ℝ≥0) :
    halfEndSourceToAngularCLM f t =
      cylinderTestL2 (halfEndSourceCylinderCLM f) (halfEndSourceCylinderCLM f).continuous t := rfl

theorem halfEndSourceToAngularCLM_norm_le (f : HalfEndSourceValue) :
    ‖halfEndSourceToAngularCLM f‖ ≤ ‖nativeSphereL2Inclusion‖ * ‖f‖ := by
  apply (BoundedContinuousFunction.norm_compContinuous_le _ _).trans
  exact (cylinderToAngularL2CLM_norm_le _).trans
    (mul_le_mul_of_nonneg_left (halfEndSourceCylinderCLM_norm_le f)
      (norm_nonneg nativeSphereL2Inclusion))

/-- The actual H2 graph supplies the source curve by a continuous linear
map.  Neither a curve nor its bound has to be supplied as an extra input. -/
def halfEndH2SourceToAngularCLM : HalfEndPhysicalH2SourceGraph →L[ℝ]
    (ℝ≥0 →ᵇ AngularL2) :=
  halfEndSourceToAngularCLM.comp halfEndPhysicalH2SourceGraphValue

theorem halfEndSourceToAngularCLM_ae (f : HalfEndSourceValue) (t : ℝ≥0) :
    (halfEndSourceToAngularCLM f t : S → ℝ) =ᵐ[angularVolume]
      fun θ => -halfEndSourceExtension f (Real.exp (-(t : ℝ)) • (θ : E)) := by
  apply (cylinderTestL2_ae _ (halfEndSourceCylinderCLM f).continuous t).trans
  exact Eventually.of_forall fun θ => halfEndSourceCylinderCLM_apply_nonneg f t.2 θ

/-- Pointwise reconstruction of the source, with the original sign and
coefficient eight, on the physical half-end. -/
theorem halfEndSourceCylinder_physicalForcing (f : HalfEndSourceValue)
    {x : E} (hx : x ≠ 0) (hx1 : ‖x‖ ≤ 1) :
    physicalForcing (fun p : ℝ × S =>
      Real.exp (-2 * p.1) * halfEndSourceCylinderCLM f p) x =
      8 * radialScale ‖x‖ * halfEndSourceExtension f x := by
  rw [physicalForcing_expNegTwo]
  let y : puncturedSpace := ⟨x, hx⟩
  have ht : 0 ≤ -Real.log ‖x‖ :=
    neg_nonneg.mpr (Real.log_nonpos (norm_nonneg x) hx1)
  have he : Real.exp (-(-Real.log ‖x‖)) = ‖x‖ := by
    rw [neg_neg, Real.exp_log (norm_pos_iff.mpr hx)]
  have hr := norm_smul_sphereDirection y
  change -8 * cylinderLift (halfEndSourceCylinderCLM f) (y : E) = _
  rw [cylinderLift_coe]
  change -8 * (radialScale ‖x‖ *
    halfEndSourceCylinderCLM f (-Real.log ‖x‖, sphereDirection y)) = _
  rw [halfEndSourceCylinderCLM_apply_nonneg f ht, he, hr]
  ring

#print axioms halfEndH2SourceToAngularCLM
#print axioms halfEndSourceCylinder_physicalForcing

end Yamabe3.Analysis.UniformElliptic
