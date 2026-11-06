import Yamabe3.Analysis.NativeHalfEndEnergyEntrance
import Yamabe3.Analysis.SpectralIntegralWeightedCauchy

/-!
# Strong Cauchy data of the actual high half-end potential solution

The boundary input is the real native angular H1 completion.  Its actual
reciprocal entrance diagonal supplies another element of that same space.
The constructed physical curve is the genuine free Poisson curve of this
auxiliary datum minus the same full-line potential correction.  Both terms
have strong Hilbert derivatives, including the right derivative at zero.
The constants retain exactly kappa < 1, and no H4 regularity at the
entrance is inferred from an H1 datum.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Set Filter MeasureTheory PoincareMT
open scoped Topology lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

open SphereSpectrum

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

private def halfAuxiliaryCoordinates (b : AngularH1) : SpectralSpace AngularIndex :=
  angularBasis.repr (angularEmbedding (nativeHighEnergyEntranceCLM hκ0 hκ1 V hV hV0 b))

private def halfCorrectionSource (b : AngularH1) : ℝ →ᵇ SpectralSpace AngularIndex :=
  V • spectralFullBoundaryPoissonCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
    (halfAuxiliaryCoordinates hκ0 hκ1 V hV hV0 b)

private def halfCorrection (b : AngularH1) : ℝ →ᵇ SpectralSpace AngularIndex :=
  spectralHalfFullPotentialCorrectionCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
    hκ0 hκ1 V hV (halfAuxiliaryCoordinates hκ0 hκ1 V hV hV0 b)

private theorem halfCorrection_eq_same_inverse (b : AngularH1) :
    halfCorrection hκ0 hκ1 V hV hV0 b =
      spectralIntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
        (by norm_num : |(-2 : ℝ)| < (5 / 2 : ℝ)) hκ0 hκ1 V hV
        (halfCorrectionSource hκ0 hκ1 V hV hV0 b) := rfl

private theorem halfAuxiliaryCoordinates_norm_le (b : AngularH1) :
    ‖halfAuxiliaryCoordinates hκ0 hκ1 V hV hV0 b‖ ≤ ‖b‖ := by
  rw [halfAuxiliaryCoordinates, LinearIsometryEquiv.norm_map]
  exact (PoincareMT.LeviCivitaData.Dirichlet.norm_toDomainL2_le _).trans
    (nativeHighEnergyEntranceCLM_norm_le hκ0 hκ1 V hV hV0 b)

private theorem halfCorrectionForcing_norm_le (b : AngularH1) :
    ‖halfCorrectionSource hκ0 hκ1 V hV hV0 b - V • halfCorrection hκ0 hκ1 V hV hV0 b‖ ≤
      (‖V‖ / (1 - κ)) * ‖b‖ := by
  let a := halfAuxiliaryCoordinates hκ0 hκ1 V hV hV0 b
  have hκ : 0 < 1 - κ := sub_pos.mpr hκ1
  have hQ := spectralFullBoundaryPoissonCLM_apply_norm_le nativeAngularRate
    (by norm_num) nativeAngularRate_lower a
  have hC := spectralHalfFullPotentialCorrectionCLM_norm_le nativeAngularRate
    (by norm_num) nativeAngularRate_lower hκ0 hκ1 V hV a
  calc
    _ ≤ ‖halfCorrectionSource hκ0 hκ1 V hV hV0 b‖ +
        ‖V • halfCorrection hκ0 hκ1 V hV hV0 b‖ := norm_sub_le _ _
    _ ≤ ‖V‖ * ‖a‖ + ‖V‖ * ((κ / (1 - κ)) * ‖a‖) := add_le_add
      ((norm_smul_le V _).trans (mul_le_mul_of_nonneg_left hQ (norm_nonneg V)))
      ((norm_smul_le V _).trans (mul_le_mul_of_nonneg_left hC (norm_nonneg V)))
    _ = (‖V‖ / (1 - κ)) * ‖a‖ := by field_simp [hκ.ne']; ring
    _ ≤ (‖V‖ / (1 - κ)) * ‖b‖ := mul_le_mul_of_nonneg_left
      (halfAuxiliaryCoordinates_norm_le hκ0 hκ1 V hV hV0 b)
      (div_nonneg (norm_nonneg V) hκ.le)

/-- Remove the already specified common exp(2t) weight from the actual
constructed half-end curve.  The extension to negative t is only a
convenient total function; all half-end conclusions use t >= 0. -/
def nativeHalfHighPotentialPhysical (b : AngularH1) (t : ℝ) : AngularL2 :=
  Real.exp (-2 * t) • nativeHalfHighPotentialPoissonCLM hκ0 hκ1 V hV hV0 b t.toNNReal

private theorem physical_full_poisson_eq_native_free
    (b : AngularH1) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-2 * t) • angularBasis.repr.symm
      (spectralFullBoundaryPoissonCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
        (halfAuxiliaryCoordinates hκ0 hκ1 V hV hV0 b) t) =
      nativeHighFreePoisson t.toNNReal
        (angularEmbedding (nativeHighEnergyEntranceCLM hκ0 hκ1 V hV hV0 b)) := by
  apply angularBasis.repr.injective
  ext i
  rw [map_smul, LinearIsometryEquiv.apply_symm_apply]
  change Real.exp (-2 * t) *
    spectralFullBoundaryPoissonCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
      (halfAuxiliaryCoordinates hκ0 hκ1 V hV hV0 b) t i = _
  rw [spectralFullBoundaryPoissonCLM_coordinate, abs_of_nonneg ht]
  have hcoeff := congrArg (fun u : AngularL2 => inner ℝ (angularBasis i) u)
    (nativeHighEnergyEntranceCLM_embedding_high hκ0 hκ1 V hV hV0 b)
  rw [nativeHighProjection, nativeAngularProjection_coefficient] at hcoeff
  rw [HilbertBasis.repr_apply_apply, nativeHighFreePoisson_coefficient,
    Real.coe_toNNReal t ht, hcoeff]
  simp only [halfAuxiliaryCoordinates, HilbertBasis.repr_apply_apply]
  change Real.exp (-2 * t) * (Real.exp (2 * t - nativeAngularRate i * t) *
    inner ℝ (angularBasis i)
      (angularEmbedding (nativeHighEnergyEntranceCLM hκ0 hκ1 V hV hV0 b))) = _
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The physical curve is literally the same free Poisson term minus the
same canonical potential correction.  This equality supplies its actual
strong derivative; it is not a separate selected representative. -/
theorem nativeHalfHighPotentialPhysical_eq_sub (b : AngularH1) (t : ℝ) (ht : 0 ≤ t) :
    nativeHalfHighPotentialPhysical hκ0 hκ1 V hV hV0 b t =
      nativeHighFreePoisson t.toNNReal
        (angularEmbedding (nativeHighEnergyEntranceCLM hκ0 hκ1 V hV hV0 b)) -
      angularBasis.repr.symm (Real.exp (-2 * t) • halfCorrection hκ0 hκ1 V hV hV0 b t) := by
  rw [nativeHalfHighPotentialPhysical, nativeHalfHighPotentialPoissonCLM_apply,
    spectralHalfPotentialPoissonCLM_apply]
  rw [← nativeHighEnergyEntranceCLM_embedding_repr hκ0 hκ1 V hV hV0 b,
    Real.coe_toNNReal t ht, map_sub, smul_sub, map_smul]
  have hfree := physical_full_poisson_eq_native_free hκ0 hκ1 V hV hV0 b t ht
  simp only [halfAuxiliaryCoordinates] at hfree
  rw [hfree]
  rfl

/-- A genuine continuous angular L2 derivative of that very physical
curve, including the right entrance derivative. -/
def nativeHalfHighPotentialPhysicalDerivative (b : AngularH1) (t : ℝ) : AngularL2 :=
  nativeHighFreePoissonDerivative (nativeHighEnergyEntranceCLM hκ0 hκ1 V hV hV0 b) t -
    angularBasis.repr.symm (Real.exp (-2 * t) •
      spectralFirstDerivativeConvolution nativeAngularRate (by norm_num) nativeAngularRate_lower
        (-2) (halfCorrectionSource hκ0 hκ1 V hV hV0 b -
          V • halfCorrection hκ0 hκ1 V hV hV0 b) t)

theorem nativeHalfHighPotentialPhysicalDerivative_continuous (b : AngularH1) :
    Continuous (nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 b) := by
  apply (nativeHighFreePoissonDerivative_continuous _).sub
  exact angularBasis.repr.symm.continuous.comp
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id))).smul
      (spectralFirstDerivativeConvolution_continuous nativeAngularRate (by norm_num)
        nativeAngularRate_lower (by norm_num : |(-2 : ℝ)| < (5 / 2 : ℝ)) _))

theorem nativeHalfHighPotentialPhysical_hasDerivWithinAt
    (b : AngularH1) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (nativeHalfHighPotentialPhysical hκ0 hκ1 V hV hV0 b)
      (nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 b t) (Ici 0) t := by
  let A := angularBasis.repr.symm.toLinearIsometry.toContinuousLinearMap
  have hc := spectralIntegralPotentialInverse_weighted_hasDerivAt nativeAngularRate
    (by norm_num : (0 : ℝ) < 5 / 2) nativeAngularRate_lower
    (by norm_num : |(-2 : ℝ)| < (5 / 2 : ℝ)) hκ0 hκ1 V hV
    (halfCorrectionSource hκ0 hκ1 V hV hV0 b) t
  rw [← halfCorrection_eq_same_inverse hκ0 hκ1 V hV hV0 b] at hc
  have h := (nativeHighFreePoisson_hasDerivWithinAt
    (nativeHighEnergyEntranceCLM hκ0 hκ1 V hV hV0 b) t ht).sub
    (A.hasFDerivAt.comp_hasDerivAt t hc).hasDerivWithinAt
  apply h.congr_of_mem _ ht
  intro s hs
  exact nativeHalfHighPotentialPhysical_eq_sub hκ0 hκ1 V hV hV0 b s hs

theorem nativeHalfHighPotentialPhysical_hasDerivAt
    (b : AngularH1) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (nativeHalfHighPotentialPhysical hκ0 hκ1 V hV hV0 b)
      (nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 b t) t :=
  (nativeHalfHighPotentialPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 b t ht.le).hasDerivAt
    (Ici_mem_nhds ht)

theorem nativeHalfHighPotentialPhysical_zero (b : AngularH1) :
    nativeHalfHighPotentialPhysical hκ0 hκ1 V hV hV0 b 0 =
      angularEmbedding (nativeHighEnergyProjectionCLM b) := by
  simp only [nativeHalfHighPotentialPhysical, mul_zero, Real.exp_zero, one_smul,
    Real.toNNReal_zero, nativeHalfHighPotentialPoissonCLM_zero]

/-- The original exp(2t) weight controls both the literal solution and
its actual strong normal candidate, with a constant before the datum. -/
theorem nativeHalfHighPotentialPhysical_weighted_cauchy
    (b : AngularH1) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (2 * t) * ‖nativeHalfHighPotentialPhysical hκ0 hκ1 V hV hV0 b t‖ ≤
        ‖b‖ / (1 - κ) ∧
    Real.exp (2 * t) * ‖nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 b t‖ ≤
        (1 + (10 / 9 : ℝ) * ‖V‖ / (1 - κ)) * ‖b‖ := by
  have hκ : 0 < 1 - κ := sub_pos.mpr hκ1
  have he : Real.exp (2 * t) * Real.exp (-2 * t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  constructor
  · rw [nativeHalfHighPotentialPhysical, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le,
      ← mul_assoc, he, one_mul]
    exact (BoundedContinuousFunction.norm_coe_le_norm _ _).trans
      (nativeHalfHighPotentialPoissonCLM_norm_le hκ0 hκ1 V hV hV0 b)
  · let F := halfCorrectionSource hκ0 hκ1 V hV hV0 b -
      V • halfCorrection hκ0 hκ1 V hV hV0 b
    have hD : ‖spectralFirstDerivativeConvolution nativeAngularRate (by norm_num)
        nativeAngularRate_lower (-2) F t‖ ≤ (10 / 9 : ℝ) * ‖F‖ := by
      convert spectralFirstDerivativeConvolution_norm_le nativeAngularRate (by norm_num)
        nativeAngularRate_lower (by norm_num : |(-2 : ℝ)| < (5 / 2 : ℝ)) F t using 1 <;>
        norm_num <;> ring
    calc
      _ ≤ Real.exp (2 * t) *
          (‖nativeHighFreePoissonDerivative (nativeHighEnergyEntranceCLM hκ0 hκ1 V hV hV0 b) t‖ +
            ‖angularBasis.repr.symm (Real.exp (-2 * t) •
              spectralFirstDerivativeConvolution nativeAngularRate (by norm_num)
                nativeAngularRate_lower (-2) F t)‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.exp_pos _).le
      _ = Real.exp (2 * t) *
          ‖nativeHighFreePoissonDerivative (nativeHighEnergyEntranceCLM hκ0 hκ1 V hV hV0 b) t‖ +
          ‖spectralFirstDerivativeConvolution nativeAngularRate (by norm_num)
            nativeAngularRate_lower (-2) F t‖ := by
        rw [mul_add, LinearIsometryEquiv.norm_map, norm_smul,
          Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc, he, one_mul]
      _ ≤ ‖b‖ + (10 / 9 : ℝ) * ((‖V‖ / (1 - κ)) * ‖b‖) :=
        add_le_add
          (((nativeHighFreePoisson_weighted_cauchy
            (nativeHighEnergyEntranceCLM hκ0 hκ1 V hV hV0 b) t ht).2).trans
            (nativeHighEnergyEntranceCLM_norm_le hκ0 hκ1 V hV hV0 b))
          (hD.trans (mul_le_mul_of_nonneg_left
            (halfCorrectionForcing_norm_le hκ0 hκ1 V hV hV0 b) (by norm_num)))
      _ = _ := by ring

#print axioms nativeHalfHighPotentialPhysical_eq_sub
#print axioms nativeHalfHighPotentialPhysical_hasDerivWithinAt
#print axioms nativeHalfHighPotentialPhysical_zero
#print axioms nativeHalfHighPotentialPhysical_weighted_cauchy

end Yamabe3.Analysis.Delaunay
