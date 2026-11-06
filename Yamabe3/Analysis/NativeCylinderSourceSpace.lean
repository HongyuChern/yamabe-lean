import Yamabe3.Analysis.NativeCylinderTestCurve
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Actual continuous scalar sources and their native Hilbert curves

The source Banach space is the real bounded continuous functions on the
actual native cylinder. Currying into continuous sphere functions is a
norm-one linear map. The genuine finite-volume L2 inclusion then yields a
bounded linear map into bounded continuous native angular Hilbert curves.
Exponential conjugation is an explicit scalar function, not a new PDE.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

open SpherePolar SphereSpectrum Poincare.Geometry.Riemannian.SpaceForm

abbrev CylinderSource := (ℝ × S) →ᵇ ℝ

def cylinderBoundedCurry (F : CylinderSource) : ℝ →ᵇ C(S, ℝ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (ContinuousMap.curry F.toContinuousMap)
    (ContinuousMap.curry F.toContinuousMap).continuous ‖F‖ (fun t => by
      apply (ContinuousMap.norm_le _ (norm_nonneg F)).mpr
      intro θ
      exact F.norm_coe_le_norm (t, θ))

theorem cylinderBoundedCurry_norm_le (F : CylinderSource) :
    ‖cylinderBoundedCurry F‖ ≤ ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
  intro t
  apply (ContinuousMap.norm_le _ (norm_nonneg F)).mpr
  intro θ
  exact F.norm_coe_le_norm (t, θ)

def cylinderBoundedCurryCLM : CylinderSource →L[ℝ] (ℝ →ᵇ C(S, ℝ)) :=
  LinearMap.mkContinuous
    { toFun := cylinderBoundedCurry
      map_add' := fun F G => by ext t θ; rfl
      map_smul' := fun c F => by ext t θ; rfl }
    1 (fun F => by
      change ‖cylinderBoundedCurry F‖ ≤ 1 * ‖F‖
      simpa only [one_mul] using cylinderBoundedCurry_norm_le F)

def nativeSphereL2Inclusion : C(S, ℝ) →L[ℝ] AngularL2 :=
  ContinuousMap.toLp 2 ((roundSphereMetric 2).volumeMeasure.restrict univ) ℝ

def cylinderToAngularL2CLM : CylinderSource →L[ℝ] (ℝ →ᵇ AngularL2) :=
  (nativeSphereL2Inclusion.compLeftContinuousBounded ℝ).comp cylinderBoundedCurryCLM

theorem cylinderToAngularL2CLM_apply (F : CylinderSource) (t : ℝ) :
    cylinderToAngularL2CLM F t = cylinderTestL2 F F.continuous t := rfl

theorem cylinderToAngularL2CLM_norm_le (F : CylinderSource) :
    ‖cylinderToAngularL2CLM F‖ ≤ ‖nativeSphereL2Inclusion‖ * ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le (f := cylinderToAngularL2CLM F)
    (mul_nonneg (norm_nonneg nativeSphereL2Inclusion) (norm_nonneg F))).mpr
  intro t
  change ‖nativeSphereL2Inclusion ((cylinderBoundedCurry F) t)‖ ≤ _
  exact nativeSphereL2Inclusion.le_opNorm_of_le
    (((cylinderBoundedCurry F).norm_coe_le_norm t).trans (cylinderBoundedCurry_norm_le F))

theorem cylinderToAngularL2CLM_sub_norm_le (F G : CylinderSource) :
    ‖cylinderToAngularL2CLM F - cylinderToAngularL2CLM G‖ ≤
      ‖nativeSphereL2Inclusion‖ * ‖F - G‖ := by
  rw [← map_sub]
  exact cylinderToAngularL2CLM_norm_le (F - G)

def weightedCylinderSource (δ : ℝ) (F : CylinderSource) (p : ℝ × S) : ℝ :=
  Real.exp (δ * p.1) * F p

theorem continuous_weightedCylinderSource (δ : ℝ) (F : CylinderSource) :
    Continuous (weightedCylinderSource δ F) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul F.continuous

theorem smooth_weightedCylinderSource (δ : ℝ) {F : CylinderSource}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (F : ℝ × S → ℝ)) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (weightedCylinderSource δ F) := by
  exact ((Real.contDiff_exp.contMDiff).comp (contMDiff_const.mul contMDiff_fst)).mul hF

theorem cylinderTestL2_weightedCylinderSource (δ : ℝ) (F : CylinderSource) (t : ℝ) :
    cylinderTestL2 (weightedCylinderSource δ F) (continuous_weightedCylinderSource δ F) t =
      Real.exp (δ * t) • cylinderToAngularL2CLM F t := by
  change nativeSphereL2Inclusion
      (cylinderTestContinuous (weightedCylinderSource δ F) (continuous_weightedCylinderSource δ F) t) =
    Real.exp (δ * t) • nativeSphereL2Inclusion ((cylinderBoundedCurry F) t)
  rw [← map_smul]
  rfl

theorem norm_weightedCylinderSource_le (δ : ℝ) (F : CylinderSource) (p : ℝ × S) :
    ‖weightedCylinderSource δ F p‖ ≤ ‖F‖ * Real.exp (δ * p.1) := by
  rw [weightedCylinderSource, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left (F.norm_coe_le_norm p) (Real.exp_pos _).le).trans_eq
    (mul_comm _ _)

theorem norm_weightedCylinderSource_sub_le (δ : ℝ) (F G : CylinderSource) (p : ℝ × S) :
    ‖weightedCylinderSource δ F p - weightedCylinderSource δ G p‖ ≤
      ‖F - G‖ * Real.exp (δ * p.1) := by
  have h := norm_weightedCylinderSource_le δ (F - G) p
  simpa only [weightedCylinderSource, BoundedContinuousFunction.sub_apply, mul_sub] using h

theorem norm_native_weighted_source_le (δ : ℝ) (F : CylinderSource) (t : ℝ) :
    ‖cylinderTestL2 (weightedCylinderSource δ F) (continuous_weightedCylinderSource δ F) t‖ ≤
      (‖nativeSphereL2Inclusion‖ * ‖F‖) * Real.exp (δ * t) := by
  rw [cylinderTestL2_weightedCylinderSource, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left
    (((cylinderToAngularL2CLM F).norm_coe_le_norm t).trans (cylinderToAngularL2CLM_norm_le F))
    (Real.exp_pos _).le).trans_eq (mul_comm _ _)

#print axioms cylinderToAngularL2CLM
#print axioms cylinderToAngularL2CLM_sub_norm_le
#print axioms cylinderTestL2_weightedCylinderSource

end Yamabe3.Analysis.Delaunay
