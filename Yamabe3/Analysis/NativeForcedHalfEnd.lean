import Yamabe3.Analysis.SpectralHalfEndForcedInverse
import Yamabe3.Analysis.NativeAngularProjections

/-!
# The actual native high forced half-end with zero Dirichlet entrance

The original native L2 source is first projected onto the true high
angular spectrum.  Its actual Hilbert coordinates enter the constructed
same-potential spectral Dirichlet inverse.  Native synthesis and the
literal factor `exp (-2*t)` define the original physical curve.

Low coordinates vanish by the actual inverse's invariant.  This removes
the auxiliary clipped rates and proves the equation with the true native
angular eigenvalues.  All positive-time C2 claims concern the same actual
coordinates; no smooth-source hypothesis or replacement representative
is introduced.  The totalization with `toNNReal` is only claimed
continuous at the entrance.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

open SphereSpectrum

/-- Coordinates of the actual high projection of the half-line source. -/
def nativeHalfHighSourceCoordinatesCLM :
    (ℝ≥0 →ᵇ AngularL2) →L[ℝ] (ℝ≥0 →ᵇ SpectralSpace AngularIndex) :=
  (angularBasis.repr.toLinearIsometry.toContinuousLinearMap.comp
    nativeHighProjection).compLeftContinuousBounded ℝ≥0

theorem nativeHalfHighSourceCoordinatesCLM_apply
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ≥0) (i : AngularIndex) :
    nativeHalfHighSourceCoordinatesCLM F t i =
      inner ℝ (angularBasis i) (nativeHighProjection (F t)) :=
  HilbertBasis.repr_apply_apply angularBasis (nativeHighProjection (F t)) i

theorem nativeHalfHighSourceCoordinatesCLM_norm_le (F : ℝ≥0 →ᵇ AngularL2) :
    ‖nativeHalfHighSourceCoordinatesCLM F‖ ≤ ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
  intro t
  change ‖angularBasis.repr (nativeHighProjection (F t))‖ ≤ ‖F‖
  rw [LinearIsometryEquiv.norm_map]
  exact (nativeAngularProjection_apply_norm_le _ (F t)).trans (F.norm_coe_le_norm t)

theorem nativeHalfHighSourceCoordinatesCLM_low_zero
    (F : ℝ≥0 →ᵇ AngularL2) (i : AngularIndex) (hi : angularEigenvalue i < 6)
    (t : ℝ≥0) : nativeHalfHighSourceCoordinatesCLM F t i = 0 := by
  rw [nativeHalfHighSourceCoordinatesCLM_apply, nativeHighProjection,
    nativeAngularProjection_coefficient, if_neg (not_le.mpr hi)]

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The genuine native bounded weighted solution operator. -/
def nativeHalfHighDirichletCLM :
    (ℝ≥0 →ᵇ AngularL2) →L[ℝ] (ℝ≥0 →ᵇ AngularL2) :=
  (angularBasis.repr.symm.toLinearIsometry.toContinuousLinearMap.compLeftContinuousBounded ℝ≥0).comp
    ((spectralHalfPotentialDirichletCLM nativeAngularRate (by norm_num)
      nativeAngularRate_lower hκ0 hκ1 V hV hV0).comp nativeHalfHighSourceCoordinatesCLM)

theorem nativeHalfHighDirichletCLM_apply
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ≥0) :
    nativeHalfHighDirichletCLM hκ0 hκ1 V hV hV0 F t =
      angularBasis.repr.symm (spectralHalfPotentialDirichletCLM nativeAngularRate
        (by norm_num) nativeAngularRate_lower hκ0 hκ1 V hV hV0
        (nativeHalfHighSourceCoordinatesCLM F) t) := rfl

theorem nativeHalfHighDirichletCLM_coefficient
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ≥0) (i : AngularIndex) :
    inner ℝ (angularBasis i) (nativeHalfHighDirichletCLM hκ0 hκ1 V hV hV0 F t) =
      spectralHalfPotentialDirichletCLM nativeAngularRate (by norm_num)
        nativeAngularRate_lower hκ0 hκ1 V hV hV0
        (nativeHalfHighSourceCoordinatesCLM F) t i := by
  rw [← HilbertBasis.repr_apply_apply, nativeHalfHighDirichletCLM_apply,
    LinearIsometryEquiv.apply_symm_apply]

theorem nativeHalfHighDirichletCLM_zero (F : ℝ≥0 →ᵇ AngularL2) :
    nativeHalfHighDirichletCLM hκ0 hκ1 V hV hV0 F 0 = 0 := by
  rw [nativeHalfHighDirichletCLM_apply, spectralHalfPotentialDirichletCLM_zero, map_zero]

theorem nativeHalfHighDirichletCLM_norm_le (F : ℝ≥0 →ᵇ AngularL2) :
    ‖nativeHalfHighDirichletCLM hκ0 hκ1 V hV hV0 F‖ ≤
      (2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) * ‖F‖ := by
  have hc : 0 ≤ 2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2) := by positivity
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hc (norm_nonneg F))).mpr
  intro t
  rw [nativeHalfHighDirichletCLM_apply, LinearIsometryEquiv.norm_map]
  exact ((BoundedContinuousFunction.norm_coe_le_norm _ _).trans
    (spectralHalfPotentialDirichletCLM_apply_norm_le nativeAngularRate (by norm_num)
      nativeAngularRate_lower hκ0 hκ1 V hV hV0 (nativeHalfHighSourceCoordinatesCLM F))).trans
        (mul_le_mul_of_nonneg_left (nativeHalfHighSourceCoordinatesCLM_norm_le F) hc)

theorem nativeHalfHighDirichletCLM_low_zero
    (F : ℝ≥0 →ᵇ AngularL2) (i : AngularIndex) (hi : angularEigenvalue i < 6)
    (t : ℝ≥0) :
    inner ℝ (angularBasis i) (nativeHalfHighDirichletCLM hκ0 hκ1 V hV hV0 F t) = 0 := by
  rw [nativeHalfHighDirichletCLM_coefficient]
  exact spectralHalfPotentialDirichletCLM_coordinate_zero nativeAngularRate (by norm_num)
    nativeAngularRate_lower hκ0 hκ1 V hV hV0 (nativeHalfHighSourceCoordinatesCLM F) i
    (nativeHalfHighSourceCoordinatesCLM_low_zero F i hi) t

/-- The original physical angular curve.  Its time totalization is
continuous everywhere and identically zero at nonpositive time. -/
def nativeHalfHighDirichletPhysical (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ) : AngularL2 :=
  Real.exp (-2 * t) • nativeHalfHighDirichletCLM hκ0 hκ1 V hV hV0 F t.toNNReal

theorem nativeHalfHighDirichletPhysical_continuous (F : ℝ≥0 →ᵇ AngularL2) :
    Continuous (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    ((nativeHalfHighDirichletCLM hκ0 hκ1 V hV hV0 F).continuous.comp continuous_real_toNNReal)

theorem nativeHalfHighDirichletPhysical_zero_of_nonpos
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ) (ht : t ≤ 0) :
    nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t = 0 := by
  rw [nativeHalfHighDirichletPhysical, Real.toNNReal_of_nonpos ht,
    nativeHalfHighDirichletCLM_zero, smul_zero]

theorem nativeHalfHighDirichletPhysical_coefficient
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ) (i : AngularIndex) :
    inner ℝ (angularBasis i) (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t) =
      Real.exp (-2 * t) * spectralHalfPotentialDirichletCLM nativeAngularRate
        (by norm_num) nativeAngularRate_lower hκ0 hκ1 V hV hV0
        (nativeHalfHighSourceCoordinatesCLM F) t.toNNReal i := by
  rw [nativeHalfHighDirichletPhysical, real_inner_smul_right,
    nativeHalfHighDirichletCLM_coefficient]

theorem nativeHalfHighDirichletPhysical_low_zero
    (F : ℝ≥0 →ᵇ AngularL2) (i : AngularIndex) (hi : angularEigenvalue i < 6)
    (t : ℝ) :
    inner ℝ (angularBasis i) (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t) = 0 := by
  rw [nativeHalfHighDirichletPhysical, real_inner_smul_right,
    nativeHalfHighDirichletCLM_low_zero hκ0 hκ1 V hV hV0 F i hi, mul_zero]

theorem nativeHalfHighDirichletPhysical_high
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ) :
    nativeHighProjection (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t) =
      nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t := by
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply]
  rw [nativeHighProjection, nativeAngularProjection_coefficient]
  split_ifs with hi
  · rfl
  · exact (nativeHalfHighDirichletPhysical_low_zero hκ0 hκ1 V hV hV0 F i
      (lt_of_not_ge hi) t).symm

theorem nativeHalfHighDirichletPhysical_norm_le
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ) :
    ‖nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t‖ ≤
      Real.exp (-2 * t) *
        ((2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) * ‖F‖) := by
  rw [nativeHalfHighDirichletPhysical, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left
    (((nativeHalfHighDirichletCLM hκ0 hκ1 V hV hV0 F).norm_coe_le_norm _).trans
      (nativeHalfHighDirichletCLM_norm_le hκ0 hκ1 V hV hV0 F)) (Real.exp_pos _).le

theorem nativeHalfHighDirichletPhysical_coefficient_c2
    (F : ℝ≥0 →ᵇ AngularL2) (i : AngularIndex) :
    ContDiffOn ℝ 2 (fun t => inner ℝ (angularBasis i)
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t)) (Ioi 0) := by
  simp only [nativeHalfHighDirichletPhysical_coefficient]
  exact spectralHalfPotentialDirichletCLM_physical_coordinate_c2 nativeAngularRate
    (by norm_num) nativeAngularRate_lower hκ0 hκ1 V hV hV0
    (nativeHalfHighSourceCoordinatesCLM F) i

/-- The true native eigenvalue equation follows after proving that every
low coordinate of this same field vanishes. -/
theorem nativeHalfHighDirichletPhysical_coefficient_equation
    (F : ℝ≥0 →ᵇ AngularL2) (i : AngularIndex) (t : ℝ) (ht : 0 < t) :
    let z := fun s => inner ℝ (angularBasis i)
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F s)
    HasDerivAt (deriv z)
      ((angularEigenvalue i + 1 / 4 - V t) * z t + Real.exp (-2 * t) *
        inner ℝ (angularBasis i) (nativeHighProjection (F t.toNNReal))) t := by
  let z := fun s => inner ℝ (angularBasis i)
    (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F s)
  have he : z = fun s : ℝ => Real.exp (-2 * s) *
      spectralHalfPotentialDirichletCLM nativeAngularRate (by norm_num)
        nativeAngularRate_lower hκ0 hκ1 V hV hV0
        (nativeHalfHighSourceCoordinatesCLM F) s.toNNReal i :=
    funext fun s => nativeHalfHighDirichletPhysical_coefficient hκ0 hκ1 V hV hV0 F s i
  have hraw := spectralHalfPotentialDirichletCLM_physical_coordinate_equation nativeAngularRate
    (by norm_num) nativeAngularRate_lower hκ0 hκ1 V hV hV0
    (nativeHalfHighSourceCoordinatesCLM F) i t ht
  dsimp only at hraw
  have h : HasDerivAt (deriv z)
      ((nativeAngularRate i ^ 2 - V t) * z t + Real.exp (-2 * t) *
        inner ℝ (angularBasis i) (nativeHighProjection (F t.toNNReal))) t := by
    simpa only [he, nativeHalfHighSourceCoordinatesCLM_apply] using hraw
  change HasDerivAt (deriv z)
    ((angularEigenvalue i + 1 / 4 - V t) * z t + Real.exp (-2 * t) *
      inner ℝ (angularBasis i) (nativeHighProjection (F t.toNNReal))) t
  apply h.congr_deriv
  by_cases hi : 6 ≤ angularEigenvalue i
  · rw [nativeAngularRate_sq, max_eq_right hi]
  · have hz : z t = 0 := nativeHalfHighDirichletPhysical_low_zero hκ0 hκ1 V hV hV0 F i
      (lt_of_not_ge hi) t
    simp only [hz, mul_zero]

#print axioms nativeHalfHighSourceCoordinatesCLM
#print axioms nativeHalfHighDirichletCLM
#print axioms nativeHalfHighDirichletCLM_norm_le
#print axioms nativeHalfHighDirichletPhysical_zero_of_nonpos
#print axioms nativeHalfHighDirichletPhysical_continuous
#print axioms nativeHalfHighDirichletPhysical_high
#print axioms nativeHalfHighDirichletPhysical_coefficient_c2
#print axioms nativeHalfHighDirichletPhysical_coefficient_equation

end Yamabe3.Analysis.Delaunay
