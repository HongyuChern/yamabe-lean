import Yamabe3.Analysis.SpectralHalfEndDirichlet
import Yamabe3.Analysis.SpectralPositivePotentialOrder

/-!
# Actual entrance inversion for the same nonnegative potential

The full-line free Poisson extension Q has norm at most one.  Correcting
it by the already proved same-potential inverse gives Q - R_V(V Q), whose
positive-time equation is homogeneous.  Its entrance map is I - T, where
T = evaluation_at_zero R_V V Q is an actual diagonal nonpositive map.
The reciprocal diagonal of I - T is consequently bounded by one. This
uses the sign of the true Green kernel, not a stronger kappa < 1/2
hypothesis. It also contracts any already existing spectral square root
of the boundary datum, a fact needed for the actual H1 entrance derivative.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped NNReal Topology lp BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

section FreeExtension

variable {ι : Type*} (k : ι → ℝ) {k₀ : ℝ} (hk₀ : 2 < k₀) (hk : ∀ i, k₀ ≤ k i)

/-- The actual weighted full-line even physical Poisson extension. -/
def spectralFullBoundaryPoissonCLM : SpectralSpace ι →L[ℝ] (ℝ →ᵇ SpectralSpace ι) :=
  halfEndPhysicalEvenExtensionCLM.comp (spectralHalfPoissonCLM k hk₀ hk)

theorem spectralFullBoundaryPoissonCLM_coordinate (b : SpectralSpace ι) (t : ℝ) (i : ι) :
    spectralFullBoundaryPoissonCLM k hk₀ hk b t i =
      Real.exp (2 * t - k i * |t|) * b i := by
  change Real.exp (2 * t - 2 * |t|) *
    (spectralHalfPoisson k hk₀ hk b ⟨|t|, abs_nonneg t⟩ i) = _
  rw [spectralHalfPoisson_coordinate]
  change Real.exp (2 * t - 2 * |t|) * (Real.exp ((2 - k i) * |t|) * b i) = _
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem spectralFullBoundaryPoissonCLM_zero (b : SpectralSpace ι) :
    spectralFullBoundaryPoissonCLM k hk₀ hk b 0 = b := by
  ext i
  simp only [spectralFullBoundaryPoissonCLM_coordinate, abs_zero, mul_zero,
    sub_zero, Real.exp_zero, one_mul]

theorem spectralFullBoundaryPoissonCLM_apply_norm_le (b : SpectralSpace ι) :
    ‖spectralFullBoundaryPoissonCLM k hk₀ hk b‖ ≤ ‖b‖ :=
  (halfEndPhysicalEvenExtension_norm_le (spectralHalfPoisson k hk₀ hk b)).trans
    (spectralHalfPoisson_norm_le k hk₀ hk b)

end FreeExtension

private def spectralPotentialMultiplyCLM {ι : Type*} (V : ℝ →ᵇ ℝ) :
    (ℝ →ᵇ SpectralSpace ι) →L[ℝ] (ℝ →ᵇ SpectralSpace ι) :=
  ({ toFun := fun U => V • U
     map_add' := by
       intro U W
       apply BoundedContinuousFunction.ext
       intro t
       change V t • (U t + W t) = V t • U t + V t • W t
       exact smul_add _ _ _
     map_smul' := by
       intro c U
       apply BoundedContinuousFunction.ext
       intro t
       change V t • (c • U t) = c • (V t • U t)
       exact smul_comm _ _ _ } :
      (ℝ →ᵇ SpectralSpace ι) →ₗ[ℝ] (ℝ →ᵇ SpectralSpace ι)).mkContinuous ‖V‖
    (fun U => by
      change ‖V • U‖ ≤ ‖V‖ * ‖U‖
      exact norm_smul_le V U)

section Entrance

variable {ι : Type*} (k : ι → ℝ) {k₀ κ : ℝ}
  (hk₀ : 2 < k₀) (hk : ∀ i, k₀ ≤ k i) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
  (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The correction is the previously constructed canonical R_V, applied
to the actual potential times the actual free Poisson curve. -/
def spectralHalfFullPotentialCorrectionCLM :
    SpectralSpace ι →L[ℝ] (ℝ →ᵇ SpectralSpace ι) :=
  (spectralIntegralPotentialInverseCLM k (by linarith : 0 < k₀) hk
    (by norm_num; exact hk₀ : |(-2 : ℝ)| < k₀) hκ0 hκ1 V hV).comp
      ((spectralPotentialMultiplyCLM V).comp (spectralFullBoundaryPoissonCLM k hk₀ hk))

theorem spectralHalfFullPotentialCorrectionCLM_apply (b : SpectralSpace ι) :
    spectralHalfFullPotentialCorrectionCLM k hk₀ hk hκ0 hκ1 V hV b =
      spectralIntegralPotentialInverse k (by linarith : 0 < k₀) hk
        (by norm_num; exact hk₀ : |(-2 : ℝ)| < k₀) hκ0 hκ1 V hV
        (V • spectralFullBoundaryPoissonCLM k hk₀ hk b) := rfl

theorem spectralHalfFullPotentialCorrectionCLM_norm_le (b : SpectralSpace ι) :
    ‖spectralHalfFullPotentialCorrectionCLM k hk₀ hk hκ0 hκ1 V hV b‖ ≤
      (κ / (1 - κ)) * ‖b‖ := by
  rw [spectralHalfFullPotentialCorrectionCLM_apply]
  exact (spectralIntegralPotentialInverse_potential_source_norm_le k
    (by linarith : 0 < k₀) hk (by norm_num; exact hk₀ : |(-2 : ℝ)| < k₀)
    hκ0 hκ1 V hV (spectralFullBoundaryPoissonCLM k hk₀ hk b)).trans
      (mul_le_mul_of_nonneg_left (spectralFullBoundaryPoissonCLM_apply_norm_le k hk₀ hk b)
        (div_nonneg hκ0 (sub_pos.mpr hκ1).le))

/-- Literal evaluation at the actual entrance of that same correction. -/
def spectralHalfBoundaryCorrectionCLM : SpectralSpace ι →L[ℝ] SpectralSpace ι :=
  (BoundedContinuousFunction.evalCLM (𝕜 := ℝ) 0).comp
    (spectralHalfFullPotentialCorrectionCLM k hk₀ hk hκ0 hκ1 V hV)

theorem spectralHalfBoundaryCorrectionCLM_coordinate_zero
    (b : SpectralSpace ι) (i : ι) (hb : b i = 0) :
    spectralHalfBoundaryCorrectionCLM k hk₀ hk hκ0 hκ1 V hV b i = 0 := by
  change spectralIntegralPotentialInverse k (by linarith : 0 < k₀) hk
    (by norm_num; exact hk₀ : |(-2 : ℝ)| < k₀) hκ0 hκ1 V hV
    (V • spectralFullBoundaryPoissonCLM k hk₀ hk b) 0 i = 0
  apply spectralIntegralPotentialInverse_coordinate_zero
  intro t
  change V t * (spectralFullBoundaryPoissonCLM k hk₀ hk b t i) = 0
  rw [spectralFullBoundaryPoissonCLM_coordinate, hb, mul_zero, mul_zero]

/-- An actual diagonal entry, evaluated on the genuine lp single vector. -/
def spectralHalfBoundaryCorrectionCoefficient (i : ι) : ℝ := by
  classical
  exact spectralHalfBoundaryCorrectionCLM k hk₀ hk hκ0 hκ1 V hV (lp.single 2 i 1) i

theorem spectralHalfBoundaryCorrectionCLM_coordinate (b : SpectralSpace ι) (i : ι) :
    spectralHalfBoundaryCorrectionCLM k hk₀ hk hκ0 hκ1 V hV b i =
      spectralHalfBoundaryCorrectionCoefficient k hk₀ hk hκ0 hκ1 V hV i * b i := by
  classical
  have hz : ((b - b i • lp.single 2 i (1 : ℝ)) : SpectralSpace ι) i = 0 := by
    simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, lp.single_apply_self, mul_one, sub_self]
  have h := spectralHalfBoundaryCorrectionCLM_coordinate_zero k hk₀ hk hκ0 hκ1 V hV
    (b - b i • lp.single 2 i (1 : ℝ)) i hz
  rw [map_sub, map_smul] at h
  simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul] at h
  unfold spectralHalfBoundaryCorrectionCoefficient
  exact (sub_eq_zero.mp h).trans (mul_comm _ _)

include hV0 in
/-- The actual entrance correction has nonpositive diagonal entries.
No numerical approximation or strengthened smallness factor is used. -/
theorem spectralHalfBoundaryCorrectionCoefficient_nonpos (i : ι) :
    spectralHalfBoundaryCorrectionCoefficient k hk₀ hk hκ0 hκ1 V hV i ≤ 0 := by
  classical
  change spectralIntegralPotentialInverse k (by linarith : 0 < k₀) hk
    (by norm_num; exact hk₀ : |(-2 : ℝ)| < k₀) hκ0 hκ1 V hV
    (V • spectralFullBoundaryPoissonCLM k hk₀ hk (lp.single 2 i 1)) 0 i ≤ 0
  apply spectralIntegralPotentialInverse_coordinate_nonpos k _ hk _ hκ0 hκ1 V hV hV0
  intro t
  change 0 ≤ V t * spectralFullBoundaryPoissonCLM k hk₀ hk (lp.single 2 i 1) t i
  rw [spectralFullBoundaryPoissonCLM_coordinate, lp.single_apply_self, mul_one]
  exact mul_nonneg (hV0 t) (Real.exp_pos _).le

include hV0 in
private theorem reciprocal_entrance_bound (i : ι) :
    |(1 - spectralHalfBoundaryCorrectionCoefficient k hk₀ hk hκ0 hκ1 V hV i)⁻¹| ≤ 1 := by
  have hn := spectralHalfBoundaryCorrectionCoefficient_nonpos k hk₀ hk hκ0 hκ1 V hV hV0 i
  have hd : 1 ≤ 1 - spectralHalfBoundaryCorrectionCoefficient k hk₀ hk hκ0 hκ1 V hV i := by
    linarith
  rw [abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hd)), ← one_div]
  exact (one_div_le_one_div_of_le zero_lt_one hd).trans_eq (by norm_num)

/-- The actual reciprocal of the entrance diagonal I - T. -/
def spectralHalfEntranceInverseCLM : SpectralSpace ι →L[ℝ] SpectralSpace ι :=
  spectralDiagonal
    (fun i => (1 - spectralHalfBoundaryCorrectionCoefficient k hk₀ hk hκ0 hκ1 V hV i)⁻¹)
    zero_le_one (reciprocal_entrance_bound k hk₀ hk hκ0 hκ1 V hV hV0)

theorem spectralHalfEntranceInverseCLM_coordinate (b : SpectralSpace ι) (i : ι) :
    spectralHalfEntranceInverseCLM k hk₀ hk hκ0 hκ1 V hV hV0 b i =
      (1 - spectralHalfBoundaryCorrectionCoefficient k hk₀ hk hκ0 hκ1 V hV i)⁻¹ * b i := rfl

theorem spectralHalfEntranceInverseCLM_apply_norm_le (b : SpectralSpace ι) :
    ‖spectralHalfEntranceInverseCLM k hk₀ hk hκ0 hκ1 V hV hV0 b‖ ≤ ‖b‖ := by
  have hD : ‖spectralHalfEntranceInverseCLM k hk₀ hk hκ0 hκ1 V hV hV0‖ ≤ 1 :=
    spectralDiagonal_norm_le _ zero_le_one
      (reciprocal_entrance_bound k hk₀ hk hκ0 hκ1 V hV hV0)
  calc
    _ ≤ ‖spectralHalfEntranceInverseCLM k hk₀ hk hκ0 hκ1 V hV hV0‖ * ‖b‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖b‖ := mul_le_mul_of_nonneg_right hD (norm_nonneg b)
    _ = ‖b‖ := one_mul _

theorem spectralHalfEntranceInverseCLM_boundary_equation (b : SpectralSpace ι) :
    let a := spectralHalfEntranceInverseCLM k hk₀ hk hκ0 hκ1 V hV hV0 b
    a - spectralHalfBoundaryCorrectionCLM k hk₀ hk hκ0 hκ1 V hV a = b := by
  dsimp only
  ext i
  simp only [lp.coeFn_sub, Pi.sub_apply]
  rw [spectralHalfBoundaryCorrectionCLM_coordinate,
    spectralHalfEntranceInverseCLM_coordinate]
  have hn := spectralHalfBoundaryCorrectionCoefficient_nonpos k hk₀ hk hκ0 hκ1 V hV hV0 i
  have hd : 1 - spectralHalfBoundaryCorrectionCoefficient k hk₀ hk hκ0 hκ1 V hV i ≠ 0 := by
    linarith
  field_simp
  <;> ring

/-- The same entrance inverse commutes with every actual square-root
coordinate vector supplied by an H1 datum and does not enlarge its norm. -/
theorem spectralHalfEntranceInverseCLM_rate_commute
    (b bRoot : SpectralSpace ι) (hRoot : ∀ i, bRoot i = k i * b i) :
    (∀ i, spectralHalfEntranceInverseCLM k hk₀ hk hκ0 hκ1 V hV hV0 bRoot i =
      k i * spectralHalfEntranceInverseCLM k hk₀ hk hκ0 hκ1 V hV hV0 b i) ∧
    ‖spectralHalfEntranceInverseCLM k hk₀ hk hκ0 hκ1 V hV hV0 bRoot‖ ≤ ‖bRoot‖ := by
  refine ⟨fun i => ?_, spectralHalfEntranceInverseCLM_apply_norm_le k hk₀ hk hκ0 hκ1 V hV hV0 bRoot⟩
  rw [spectralHalfEntranceInverseCLM_coordinate,
    spectralHalfEntranceInverseCLM_coordinate, hRoot i]
  ring

/-- The resulting weighted half-end curve with prescribed entrance. Its
positive-time differential equation is established in the next source. -/
def spectralHalfPotentialPoissonCLM :
    SpectralSpace ι →L[ℝ] (ℝ≥0 →ᵇ SpectralSpace ι) :=
  (halfEndRestrictionCLM.comp
    (spectralFullBoundaryPoissonCLM k hk₀ hk -
      spectralHalfFullPotentialCorrectionCLM k hk₀ hk hκ0 hκ1 V hV)).comp
        (spectralHalfEntranceInverseCLM k hk₀ hk hκ0 hκ1 V hV hV0)

theorem spectralHalfPotentialPoissonCLM_apply (b : SpectralSpace ι) (t : ℝ≥0) :
    let a := spectralHalfEntranceInverseCLM k hk₀ hk hκ0 hκ1 V hV hV0 b
    spectralHalfPotentialPoissonCLM k hk₀ hk hκ0 hκ1 V hV hV0 b t =
      spectralFullBoundaryPoissonCLM k hk₀ hk a (t : ℝ) -
        spectralHalfFullPotentialCorrectionCLM k hk₀ hk hκ0 hκ1 V hV a (t : ℝ) := rfl

theorem spectralHalfPotentialPoissonCLM_zero (b : SpectralSpace ι) :
    spectralHalfPotentialPoissonCLM k hk₀ hk hκ0 hκ1 V hV hV0 b 0 = b := by
  rw [spectralHalfPotentialPoissonCLM_apply, NNReal.coe_zero, spectralFullBoundaryPoissonCLM_zero]
  exact spectralHalfEntranceInverseCLM_boundary_equation k hk₀ hk hκ0 hκ1 V hV hV0 b

theorem spectralHalfPotentialPoissonCLM_norm_le (b : SpectralSpace ι) :
    ‖spectralHalfPotentialPoissonCLM k hk₀ hk hκ0 hκ1 V hV hV0 b‖ ≤ ‖b‖ / (1 - κ) := by
  let a := spectralHalfEntranceInverseCLM k hk₀ hk hκ0 hκ1 V hV hV0 b
  have ha : ‖a‖ ≤ ‖b‖ := spectralHalfEntranceInverseCLM_apply_norm_le k hk₀ hk hκ0 hκ1 V hV hV0 b
  apply (BoundedContinuousFunction.norm_le (div_nonneg (norm_nonneg b) (sub_pos.mpr hκ1).le)).mpr
  intro t
  rw [spectralHalfPotentialPoissonCLM_apply]
  calc
    _ ≤ ‖spectralFullBoundaryPoissonCLM k hk₀ hk a (t : ℝ)‖ +
        ‖spectralHalfFullPotentialCorrectionCLM k hk₀ hk hκ0 hκ1 V hV a (t : ℝ)‖ := norm_sub_le _ _
    _ ≤ ‖a‖ + (κ / (1 - κ)) * ‖a‖ := add_le_add
      ((BoundedContinuousFunction.norm_coe_le_norm _ _).trans
        (spectralFullBoundaryPoissonCLM_apply_norm_le k hk₀ hk a))
      ((BoundedContinuousFunction.norm_coe_le_norm _ _).trans
        (spectralHalfFullPotentialCorrectionCLM_norm_le k hk₀ hk hκ0 hκ1 V hV a))
    _ = ‖a‖ / (1 - κ) := by
      field_simp [ne_of_gt (sub_pos.mpr hκ1)]
      <;> ring
    _ ≤ ‖b‖ / (1 - κ) := div_le_div_of_nonneg_right ha (sub_pos.mpr hκ1).le

#print axioms spectralHalfBoundaryCorrectionCoefficient_nonpos
#print axioms spectralHalfEntranceInverseCLM
#print axioms spectralHalfEntranceInverseCLM_boundary_equation
#print axioms spectralHalfEntranceInverseCLM_rate_commute
#print axioms spectralHalfPotentialPoissonCLM_zero
#print axioms spectralHalfPotentialPoissonCLM_norm_le

end Entrance

end Yamabe3.Analysis.Delaunay
