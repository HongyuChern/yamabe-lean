import Yamabe3.Analysis.SpectralCoordinateEquation
import Yamabe3.Analysis.Sphere.NativeSphereHighModes

/-!
# The actual high angular L2 inverse

The native round-sphere Hilbert basis transports the genuine time-Hilbert
convolution inverse. Below the proved spectral gap the auxiliary rates are
set to 5/2; actual zero moments force those solution coordinates to vanish,
so every coordinate satisfies the genuine native eigenvalue equation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory PoincareMT
open scoped Topology lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.SphereSpectrum
open Poincare.Geometry.Riemannian.SpaceForm

def nativeAngularRate (i : AngularIndex) : ℝ := Real.sqrt (max 6 (angularEigenvalue i) + 1 / 4)

theorem nativeAngularRate_lower (i : AngularIndex) : (5 / 2 : ℝ) ≤ nativeAngularRate i := by
  have hm : (6 : ℝ) ≤ max 6 (angularEigenvalue i) := le_max_left _ _
  have hn : 0 ≤ max 6 (angularEigenvalue i) + 1 / 4 := by linarith
  have hs := Real.sq_sqrt hn
  have hp := Real.sqrt_nonneg (max 6 (angularEigenvalue i) + 1 / 4)
  dsimp [nativeAngularRate]
  nlinarith

theorem nativeAngularRate_sq (i : AngularIndex) :
    nativeAngularRate i ^ 2 = max 6 (angularEigenvalue i) + 1 / 4 :=
  Real.sq_sqrt (by have h := le_max_left (6 : ℝ) (angularEigenvalue i); linarith)

def angularSourceCoordinates (F : ℝ →ᵇ AngularL2) : ℝ →ᵇ SpectralSpace AngularIndex :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => angularBasis.repr (F t))
    (angularBasis.repr.continuous.comp F.continuous) ‖F‖
    (fun t => by simpa only [LinearIsometryEquiv.norm_map] using F.norm_coe_le_norm t)

theorem angularSourceCoordinates_apply (F : ℝ →ᵇ AngularL2) (t : ℝ) (i : AngularIndex) :
    angularSourceCoordinates F t i = inner ℝ (angularBasis i) (F t) :=
  HilbertBasis.repr_apply_apply angularBasis (F t) i

theorem angularSourceCoordinates_norm_le (F : ℝ →ᵇ AngularL2) :
    ‖angularSourceCoordinates F‖ ≤ ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
  intro t
  change ‖angularBasis.repr (F t)‖ ≤ ‖F‖
  simpa only [LinearIsometryEquiv.norm_map] using F.norm_coe_le_norm t

/-- Actual transport back to native sphere L2 via its constructed basis. -/
def nativeAngularInverse {δ : ℝ} (hδ : |δ| < 5 / 2) (V : ℝ →ᵇ ℝ)
    (hV : ‖V‖ < (5 / 2 : ℝ) ^ 2 - δ ^ 2) (F : ℝ →ᵇ AngularL2) : ℝ →ᵇ AngularL2 :=
  let U := spectralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower hδ
    V hV (angularSourceCoordinates F)
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => angularBasis.repr.symm (U t))
    (angularBasis.repr.symm.continuous.comp U.continuous) ‖U‖
    (fun t => by simpa only [LinearIsometryEquiv.norm_map] using U.norm_coe_le_norm t)

theorem nativeAngularInverse_coefficient {δ : ℝ} (hδ : |δ| < 5 / 2) (V : ℝ →ᵇ ℝ)
    (hV : ‖V‖ < (5 / 2 : ℝ) ^ 2 - δ ^ 2) (F : ℝ →ᵇ AngularL2) (t : ℝ) (i : AngularIndex) :
    inner ℝ (angularBasis i) (nativeAngularInverse hδ V hV F t) =
      spectralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower hδ
        V hV (angularSourceCoordinates F) t i := by
  rw [← HilbertBasis.repr_apply_apply]
  change angularBasis.repr (angularBasis.repr.symm _) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem nativeAngularInverse_norm_le {δ : ℝ} (hδ : |δ| < 5 / 2) (V : ℝ →ᵇ ℝ)
    (hV : ‖V‖ < (5 / 2 : ℝ) ^ 2 - δ ^ 2) (F : ℝ →ᵇ AngularL2) :
    ‖nativeAngularInverse hδ V hV F‖ ≤ ‖F‖ / ((5 / 2 : ℝ) ^ 2 - δ ^ 2 - ‖V‖) := by
  let U := spectralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower hδ
    V hV (angularSourceCoordinates F)
  have hn : ‖nativeAngularInverse hδ V hV F‖ ≤ ‖U‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg U)).mpr
    intro t
    change ‖angularBasis.repr.symm (U t)‖ ≤ ‖U‖
    simpa only [LinearIsometryEquiv.norm_map] using U.norm_coe_le_norm t
  calc
    _ ≤ ‖U‖ := hn
    _ ≤ ‖angularSourceCoordinates F‖ / ((5 / 2 : ℝ) ^ 2 - δ ^ 2 - ‖V‖) :=
      spectralPotentialInverse_norm_le nativeAngularRate (by norm_num) nativeAngularRate_lower hδ
        V hV (angularSourceCoordinates F)
    _ ≤ _ := div_le_div_of_nonneg_right (angularSourceCoordinates_norm_le F) (sub_pos.mpr hV).le

/-- Zero actual mean and actual height moments eliminate all native low
modes, without assuming a spectral classification or a reconstruction. -/
theorem nativeAngularInverse_low_zero {δ : ℝ} (hδ : |δ| < 5 / 2) (V : ℝ →ᵇ ℝ)
    (hV : ‖V‖ < (5 / 2 : ℝ) ^ 2 - δ ^ 2) (F : ℝ →ᵇ AngularL2)
    (hmean : ∀ t, (∫ x, F t x ∂(roundSphereMetric 2).volumeMeasure) = 0)
    (hfirst : ∀ t, ∀ a : Ambient 2,
      (∫ x, height a x * F t x ∂(roundSphereMetric 2).volumeMeasure) = 0)
    (i : AngularIndex) (hi : angularEigenvalue i < 6) :
    ∀ t, inner ℝ (angularBasis i) (nativeAngularInverse hδ V hV F t) = 0 := by
  intro t
  rw [nativeAngularInverse_coefficient]
  have hFc (s : ℝ) : angularSourceCoordinates F s i = 0 := by
    rw [angularSourceCoordinates_apply]
    exact angular_coefficient_zero_of_low_moments (F s) (hmean s) (hfirst s) i hi
  exact spectralPotentialInverse_coordinate_zero nativeAngularRate (by norm_num)
    nativeAngularRate_lower hδ V hV (angularSourceCoordinates F) i hFc t

/-- Every actual angular coefficient solves its native eigenvalue equation.
The aggregate solution has already been constructed in native L2. -/
theorem nativeAngularInverse_coordinate_equation {δ : ℝ} (hδ : |δ| < 5 / 2) (V : ℝ →ᵇ ℝ)
    (hV : ‖V‖ < (5 / 2 : ℝ) ^ 2 - δ ^ 2) (F : ℝ →ᵇ AngularL2)
    (hmean : ∀ t, (∫ x, F t x ∂(roundSphereMetric 2).volumeMeasure) = 0)
    (hfirst : ∀ t, ∀ a : Ambient 2,
      (∫ x, height a x * F t x ∂(roundSphereMetric 2).volumeMeasure) = 0)
    (i : AngularIndex) :
    let u := fun t => inner ℝ (angularBasis i) (nativeAngularInverse hδ V hV F t)
    Differentiable ℝ u ∧ Differentiable ℝ (deriv u) ∧
      ∀ t, deriv (deriv u) t = -2 * δ * deriv u t +
        (angularEigenvalue i + 1 / 4 - δ ^ 2) * u t +
          inner ℝ (angularBasis i) (F t) - V t * u t := by
  dsimp only
  have hrep : (fun t => inner ℝ (angularBasis i) (nativeAngularInverse hδ V hV F t)) =
      fun t => spectralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower hδ
        V hV (angularSourceCoordinates F) t i := funext fun t => nativeAngularInverse_coefficient hδ V hV F t i
  have h := spectralPotentialInverse_coordinate_equation nativeAngularRate (by norm_num)
    nativeAngularRate_lower hδ V hV (angularSourceCoordinates F) i
  dsimp only at h
  rw [← hrep] at h
  refine ⟨h.1, h.2.1, fun t => ?_⟩
  have he := h.2.2 t
  rw [nativeAngularRate_sq, angularSourceCoordinates_apply, ← congrFun hrep t] at he
  by_cases hi : 6 ≤ angularEigenvalue i
  · simpa only [max_eq_right hi] using he
  · have hz := nativeAngularInverse_low_zero hδ V hV F hmean hfirst i (lt_of_not_ge hi) t
    simpa only [hz, mul_zero] using he

end Yamabe3.Analysis.Delaunay
