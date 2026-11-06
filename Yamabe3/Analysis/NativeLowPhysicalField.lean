import Yamabe3.Analysis.NativeLowC2Coefficients
import Yamabe3.Analysis.Cylinder.NativeFiniteC1PhysicalEquation

/-! The actual finite low part of the same continuous angular source.
The future inverse supplies C2 coefficients without a smooth-source
assumption. Its physical field satisfies the model equation, with the
original factor eight. Its actual low entrance value is retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold Topology ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.SphereSpectrum Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic

def nativeLowSource (F : ℝ →ᵇ AngularL2) : ℝ →ᵇ AngularL2 :=
  nativeProjectedSource (fun i => angularEigenvalue i < 6) F

theorem nativeLowSource_high_zero (F : ℝ →ᵇ AngularL2) (i : AngularIndex)
    (hi : 6 ≤ angularEigenvalue i) (t : ℝ) :
    inner ℝ (angularBasis i) (nativeLowSource F t) = 0 := by
  rw [nativeLowSource,nativeProjectedSource_coefficient,if_neg (not_lt.mpr hi)]

def nativeLowSolvedCurve (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (F : ℝ →ᵇ AngularL2) : ℝ →ᵇ AngularL2 :=
  nativeLowAngularInverseCLM v hv hb 2 (by norm_num) (by norm_num) (nativeLowSource F)

theorem nativeLowSolvedCurve_norm_le (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (F : ℝ →ᵇ AngularL2) :
    ‖nativeLowSolvedCurve v hv hb F‖ ≤ 2*‖F‖ := by
  have hh := nativeLowAngularInverseCLM_norm_le v hv hb
    (k:=2) (by norm_num) (by norm_num) (nativeLowSource F)
  have hf : ‖nativeLowSource F‖ ≤ ‖F‖ := nativeProjectedSource_norm_le _ F
  change ‖nativeLowSolvedCurve v hv hb F‖ ≤ _ at hh
  norm_num at hh
  linarith

def nativeLowPhysicalCoefficient (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (F : ℝ →ᵇ AngularL2)
    (i : AngularIndex) (t : ℝ) : ℝ :=
  Real.exp (-2*t)*inner ℝ (angularBasis i) (nativeLowSolvedCurve v hv hb F t)

def nativeLowPhysicalField (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (F : ℝ →ᵇ AngularL2) : E → ℝ :=
  finitePhysical nativeLowIndexFinset (nativeLowPhysicalCoefficient v hv hb F)

theorem nativeLowPhysicalCoefficient_C2_equation (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (F : ℝ →ᵇ AngularL2) (i : AngularIndex) :
    ContDiff ℝ 2 (nativeLowPhysicalCoefficient v hv hb F i) ∧
    ∀ t, deriv (deriv (nativeLowPhysicalCoefficient v hv hb F i)) t =
      (angularEigenvalue i+1/4-(15/4)*v t^4)*nativeLowPhysicalCoefficient v hv hb F i t+
      Real.exp (-2*t)*inner ℝ (angularBasis i) (nativeLowSource F t) := by
  have he := nativeLowAngularInverseCLM_weighted_coefficient_C2 v hv hb
    (k:=2) (by norm_num) (by norm_num) (nativeLowSource F) (nativeLowSource_high_zero F) i
  dsimp only at he
  refine ⟨he.1,?_⟩
  intro t
  have ht := he.2 t
  change modelJacobi v (angularEigenvalue i) (nativeLowPhysicalCoefficient v hv hb F i) t = _ at ht
  unfold modelJacobi at ht
  linarith

theorem nativeLowPhysicalField_C2 (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (F : ℝ →ᵇ AngularL2) :
    ContDiffOn ℝ 2 (nativeLowPhysicalField v hv hb F) ({(0:E)}ᶜ) := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  apply ContDiffAt.sum
  intro i hi
  exact contDiffAt_cylinderLift_separable_of_c2 (smooth_angularRepresentative i) hx
    (nativeLowPhysicalCoefficient_C2_equation v hv hb F i).1.contDiffAt

theorem nativeLowPhysicalField_radial (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (F : ℝ →ᵇ AngularL2)
    {r : ℝ} (hr : 0 < r) (θ : S) :
    nativeLowPhysicalField v hv hb F (r • (θ:E)) =
      radialScale r * Real.exp (-2*(-Real.log r))*
        nativeLowRepresentativeCLM (nativeLowSolvedCurve v hv hb F (-Real.log r)) θ := by
  rw [nativeLowPhysicalField,finitePhysical_eq_lift,cylinderLift_smul _ hr]
  rw [nativeLowRepresentativeCLM_apply]
  simp only [finiteAngular,nativeLowPhysicalCoefficient]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem nativeLowPhysicalField_entrance (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (F : ℝ →ᵇ AngularL2) (θ : S) :
    nativeLowPhysicalField v hv hb F (θ:E) =
      nativeLowRepresentativeCLM (nativeLowSolvedCurve v hv hb F 0) θ := by
  simpa [radialScale] using nativeLowPhysicalField_radial v hv hb F (r:=1) (by norm_num) θ

theorem nativeLowPhysicalField_weak_equation (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (F : ℝ →ᵇ AngularL2)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩhalf : Ω ⊆ {x : E | x ≠ 0 ∧ ‖x‖ < 1}) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ j : Fin 3,
        fderiv ℝ (nativeLowPhysicalField v hv hb F) x (EuclideanSpace.single j 1)*
          fderiv ℝ φ x (EuclideanSpace.single j 1)) =
      ∫ x in Ω, (physicalForcing
        (finiteAngular nativeLowIndexFinset (fun i t =>
          Real.exp (-2*t)*inner ℝ (angularBasis i) (nativeLowSource F t))) x / 8+
        ((15/4)*v (-Real.log ‖x‖)^4/‖x‖^2)*nativeLowPhysicalField v hv hb F x)*φ x := by
  exact native_finite_c2_physical_weak_equation hΩ hΩhalf
    (fun t => (15/4)*v t^4) nativeLowIndexFinset (nativeLowPhysicalCoefficient v hv hb F)
    (fun i t => Real.exp (-2*t)*inner ℝ (angularBasis i) (nativeLowSource F t))
    (fun i _ => (nativeLowPhysicalCoefficient_C2_equation v hv hb F i).1.contDiffOn)
    (fun i _ t _ => (nativeLowPhysicalCoefficient_C2_equation v hv hb F i).2 t)

#print axioms nativeLowSolvedCurve_norm_le
#print axioms nativeLowPhysicalCoefficient_C2_equation
#print axioms nativeLowPhysicalField_C2
#print axioms nativeLowPhysicalField_radial
#print axioms nativeLowPhysicalField_entrance
#print axioms nativeLowPhysicalField_weak_equation
end Yamabe3.Analysis.Delaunay
