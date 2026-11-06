import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Three-dimensional Euclidean polar surface measure

`sphereArea` is Mathlib's `volume.toSphere`, the canonical angular measure
obtained from actual Lebesgue volume of cones. Its total area is proved to be
`4π`, using the pinned theorem for the volume of a three-dimensional ball.
`normalizedArea` is derived from this measure, rather than supplied as an
unrelated probability measure.

The radius-R surface measure is defined by dilation with the area factor R².
The independent `coneSurface_eq_sphereAtRadius` theorem derives that factor
from an actual polar-coordinate cone of radius R: its volume factor is R³/3,
and the conversion from cone volume to surface area is 3/R.

This uses the canonical polar-area convention. Equality with a separately
constructed two-dimensional Hausdorff measure or induced Riemannian volume
is a further bridge, not assumed or claimed in this module.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

namespace GreenMass.SphereMeasure

abbrev E := EuclideanSpace ℝ (Fin 3)
abbrev UnitSphere := Metric.sphere (0 : E) 1

/-- Actual Euclidean polar surface measure, constructed from Lebesgue cones. -/
def sphereArea : Measure UnitSphere := (volume : Measure E).toSphere

/-- Canonical cone formula: area is three times actual unit-cone Lebesgue volume. -/
theorem sphereArea_apply {s : Set UnitSphere} (hs : MeasurableSet s) :
    sphereArea s = 3 * (volume : Measure E)
      (Ioo (0 : ℝ) 1 • ((Subtype.val : UnitSphere → E) '' s)) := by
  simpa [sphereArea] using (volume : Measure E).toSphere_apply' hs

instance sphereArea_isFiniteMeasure : IsFiniteMeasure sphereArea := by
  dsimp [sphereArea]
  infer_instance

theorem unitBall_real_volume : (volume : Measure E).real (ball 0 1) =
    4 * Real.pi / 3 := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_three]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

theorem sphereArea_real_univ : sphereArea.real univ = 4 * Real.pi := by
  rw [sphereArea, Measure.toSphere_real_apply_univ, unitBall_real_volume]
  norm_num
  ring

theorem sphereArea_univ : sphereArea univ = ENNReal.ofReal (4 * Real.pi) := by
  have hfin : sphereArea univ ≠ ∞ := measure_ne_top sphereArea univ
  have hreal : (sphereArea univ).toReal = 4 * Real.pi := sphereArea_real_univ
  rw [← ENNReal.ofReal_toReal hfin, hreal]

/-- The angular probability measure derived from the actual Euclidean area. -/
def normalizedArea : Measure UnitSphere :=
  (ENNReal.ofReal (4 * Real.pi))⁻¹ • sphereArea

instance normalizedArea_isProbabilityMeasure : IsProbabilityMeasure normalizedArea where
  measure_univ := by
    rw [normalizedArea, Measure.smul_apply, sphereArea_univ]
    exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

theorem sphereArea_eq_smul_normalizedArea :
    sphereArea = ENNReal.ofReal (4 * Real.pi) • normalizedArea := by
  rw [normalizedArea, smul_smul,
    ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top, one_smul]

theorem integral_sphereArea_eq (f : UnitSphere → ℝ) :
    ∫ θ, f θ ∂sphereArea =
      (4 * Real.pi) * ∫ θ, f θ ∂normalizedArea := by
  rw [sphereArea_eq_smul_normalizedArea, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity)]
  rfl

/-- Radius dilation as an actual map from the Euclidean unit sphere. -/
def dilation (R : ℝ) : UnitSphere → E := fun θ => R • (θ : E)

theorem measurable_dilation (R : ℝ) : Measurable (dilation R) := by
  exact ((continuous_subtype_val : Continuous (Subtype.val : UnitSphere → E)).const_smul R).measurable

/-- Euclidean polar surface measure at radius R, on the ambient coordinate space. -/
def sphereAtRadius (R : ℝ) : Measure E :=
  ENNReal.ofReal (R ^ 2) • Measure.map (dilation R) sphereArea

instance sphereAtRadius_isFiniteMeasure (R : ℝ) : IsFiniteMeasure (sphereAtRadius R) := by
  dsimp [sphereAtRadius]
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

/-- The exact surface-integral change of variables `dS_R = R² dω`. -/
theorem sphereAtRadius_integral (R : ℝ) (f : E → ℝ) (hf : StronglyMeasurable f) :
    ∫ y, f y ∂sphereAtRadius R =
      R ^ 2 * ∫ θ, f (R • (θ : E)) ∂sphereArea := by
  rw [sphereAtRadius, integral_smul_measure,
    integral_map_of_stronglyMeasurable (measurable_dilation R) hf,
    ENNReal.toReal_ofReal (sq_nonneg R)]
  rfl

theorem sphereAtRadius_real_univ (R : ℝ) :
    (sphereAtRadius R).real univ = (4 * Real.pi) * R ^ 2 := by
  have h := sphereAtRadius_integral R (fun _ => (1 : ℝ)) stronglyMeasurable_const
  simpa only [integral_const, smul_eq_mul, mul_one, one_mul, sphereArea_real_univ, mul_comm]
    using h

/-- The actual generalized polar-coordinate measure-preserving map in dimension 3. -/
theorem polar_measurePreserving :
    MeasurePreserving (homeomorphUnitSphereProd E)
      ((volume : Measure E).comap
        (Subtype.val : ({(0 : E)}ᶜ : Set E) → E))
      (sphereArea.prod (Measure.volumeIoiPow 2)) := by
  simpa [sphereArea] using
    (volume : Measure E).measurePreserving_homeomorphUnitSphereProd

/-- The angular distribution of Lebesgue volume in a polar cone of radius R. -/
def coneAngular (R : Ioi (0 : ℝ)) : Measure UnitSphere :=
  ((sphereArea.prod (Measure.volumeIoiPow 2)).restrict (univ ×ˢ Iio R)).fst

theorem coneAngular_eq (R : Ioi (0 : ℝ)) :
    coneAngular R = ENNReal.ofReal (R.1 ^ 3 / 3) • sphereArea := by
  ext s hs
  rw [coneAngular, Measure.fst_apply hs,
    Measure.restrict_apply (measurable_fst hs)]
  have hsets : (Prod.fst ⁻¹' s) ∩ (univ ×ˢ Iio R) = s ×ˢ Iio R := by
    ext z
    simp
  rw [hsets, Measure.prod_prod, Measure.volumeIoiPow_apply_Iio,
    Measure.smul_apply]
  norm_num [smul_eq_mul, mul_comm]

/-- Surface area obtained directly from the radius-R polar cone volume. -/
def coneSurface (R : Ioi (0 : ℝ)) : Measure E :=
  ENNReal.ofReal (3 / R.1) • Measure.map (dilation R.1) (coneAngular R)

/-- Radius dilation's R² factor follows from the actual R³ cone-volume law. -/
theorem coneSurface_eq_sphereAtRadius (R : Ioi (0 : ℝ)) :
    coneSurface R = sphereAtRadius R.1 := by
  have hRpos : 0 < R.1 := R.2
  rw [coneSurface, coneAngular_eq, Measure.map_smul, smul_smul, sphereAtRadius]
  congr 1
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hR : R.1 ≠ 0 := R.2.ne'
  field_simp

#print axioms sphereArea_apply
#print axioms unitBall_real_volume
#print axioms sphereArea_real_univ
#print axioms sphereArea_univ
#print axioms normalizedArea_isProbabilityMeasure
#print axioms sphereArea_eq_smul_normalizedArea
#print axioms integral_sphereArea_eq
#print axioms measurable_dilation
#print axioms sphereAtRadius_integral
#print axioms sphereAtRadius_real_univ
#print axioms polar_measurePreserving
#print axioms coneAngular_eq
#print axioms coneSurface_eq_sphereAtRadius

end GreenMass.SphereMeasure
