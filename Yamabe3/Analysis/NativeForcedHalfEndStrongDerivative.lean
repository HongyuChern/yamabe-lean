import Yamabe3.Analysis.NativeForcedHalfEnd
import Yamabe3.Analysis.NativeHalfEndStrongCauchy
import Yamabe3.Analysis.NativeIntegralPotentialEnergy

/-!
# The actual strong right derivative of the native forced Dirichlet curve

The boundary correction uses the actual H1 value of the same full-line
potential inverse at zero.  Its H1 membership and its exact original L2
embedding come from the established root convolution construction; they
are not supplied as additional boundary regularity assumptions.

After identifying the original `nativeHalfHighDirichletPhysical` with
that full-line term minus the original potential Poisson curve, the
existing genuine strong derivatives give a continuous AngularL2 right
derivative, including the entrance.  The uniform weighted derivative
bound concerns the actual value/normal data.  It makes no assertion about
Cauchy convergence of a spectral truncation net.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

open SphereSpectrum

/-- The actual even extension of the original high projected source. -/
def nativeHalfHighFullSource (F : ℝ≥0 →ᵇ AngularL2) : ℝ →ᵇ SpectralSpace AngularIndex :=
  halfEndPhysicalEvenExtension (nativeHalfHighSourceCoordinatesCLM F)

theorem nativeHalfHighFullSource_norm_le (F : ℝ≥0 →ᵇ AngularL2) :
    ‖nativeHalfHighFullSource F‖ ≤ ‖F‖ :=
  (halfEndPhysicalEvenExtension_norm_le (nativeHalfHighSourceCoordinatesCLM F)).trans
    (nativeHalfHighSourceCoordinatesCLM_norm_le F)

theorem nativeHalfHighFullSource_low_zero
    (F : ℝ≥0 →ᵇ AngularL2) (i : AngularIndex) (hi : angularEigenvalue i < 6) (t : ℝ) :
    nativeHalfHighFullSource F t i = 0 := by
  rw [nativeHalfHighFullSource, halfEndPhysicalEvenExtension_apply]
  change Real.exp (2 * t - 2 * |t|) *
    nativeHalfHighSourceCoordinatesCLM F ⟨|t|, abs_nonneg t⟩ i = 0
  rw [nativeHalfHighSourceCoordinatesCLM_low_zero F i hi, mul_zero]

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The very full-line fixed point used by the native Dirichlet operator. -/
def nativeHalfHighFullInverse (F : ℝ≥0 →ᵇ AngularL2) : ℝ →ᵇ SpectralSpace AngularIndex :=
  spectralIntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
    (by norm_num : |(-2 : ℝ)| < (5 / 2 : ℝ)) hκ0 hκ1 V hV (nativeHalfHighFullSource F)

theorem nativeHalfHighFullInverse_low_zero
    (F : ℝ≥0 →ᵇ AngularL2) (i : AngularIndex) (hi : angularEigenvalue i < 6) (t : ℝ) :
    nativeHalfHighFullInverse hκ0 hκ1 V hV F t i = 0 :=
  spectralIntegralPotentialInverse_coordinate_zero nativeAngularRate (by norm_num)
    nativeAngularRate_lower (by norm_num : |(-2 : ℝ)| < (5 / 2 : ℝ))
    hκ0 hκ1 V hV (nativeHalfHighFullSource F) i (nativeHalfHighFullSource_low_zero F i hi) t

theorem nativeHalfHighFullInverse_norm_le (F : ℝ≥0 →ᵇ AngularL2) :
    ‖nativeHalfHighFullInverse hκ0 hκ1 V hV F‖ ≤
      ((4 / 9 : ℝ) / (1 - κ)) * ‖F‖ := by
  have h := spectralIntegralPotentialInverse_norm_le nativeAngularRate (by norm_num)
    nativeAngularRate_lower (by norm_num : |(-2 : ℝ)| < (5 / 2 : ℝ))
    hκ0 hκ1 V hV (nativeHalfHighFullSource F)
  calc
    _ ≤ (‖nativeHalfHighFullSource F‖ / ((5 / 2 : ℝ) ^ 2 - (-2) ^ 2)) / (1 - κ) := h
    _ ≤ (‖F‖ / ((5 / 2 : ℝ) ^ 2 - (-2) ^ 2)) / (1 - κ) :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (nativeHalfHighFullSource_norm_le F) (by norm_num))
        (sub_pos.mpr hκ1).le
    _ = _ := by norm_num <;> ring

/-- The entrance H1 datum is produced from the actual root vector of
that same fixed point, before the homogeneous boundary correction. -/
def nativeHalfHighFullInverseEntranceEnergy (F : ℝ≥0 →ᵇ AngularL2) : AngularH1 :=
  nativeIntegralPotentialEnergy hκ0 hκ1 V hV (nativeHalfHighFullSource F) 0

theorem nativeHalfHighFullInverseEntranceEnergy_embedding (F : ℝ≥0 →ᵇ AngularL2) :
    angularEmbedding (nativeHalfHighFullInverseEntranceEnergy hκ0 hκ1 V hV F) =
      angularBasis.repr.symm (nativeHalfHighFullInverse hκ0 hκ1 V hV F 0) :=
  nativeIntegralPotentialEnergy_embedding hκ0 hκ1 V hV (nativeHalfHighFullSource F) 0

theorem nativeHalfHighFullInverseEntranceEnergy_norm_le (F : ℝ≥0 →ᵇ AngularL2) :
    ‖nativeHalfHighFullInverseEntranceEnergy hκ0 hκ1 V hV F‖ ≤
      (20 / 9 : ℝ) * (1 + (4 / 9 : ℝ) * ‖V‖ / (1 - κ)) * ‖F‖ := by
  have hκ : 0 < 1 - κ := sub_pos.mpr hκ1
  exact (nativeIntegralPotentialEnergy_norm_le hκ0 hκ1 V hV (nativeHalfHighFullSource F) 0).trans
    (mul_le_mul_of_nonneg_left (nativeHalfHighFullSource_norm_le F) (by positivity))

/-- No low coordinate is introduced by the actual energy representative
of the full-line entrance value. -/
theorem nativeHalfHighFullInverseEntranceEnergy_high (F : ℝ≥0 →ᵇ AngularL2) :
    nativeHighProjection
        (angularEmbedding (nativeHalfHighFullInverseEntranceEnergy hκ0 hκ1 V hV F)) =
      angularEmbedding (nativeHalfHighFullInverseEntranceEnergy hκ0 hκ1 V hV F) := by
  have hcoeff (i : AngularIndex) :
      inner ℝ (angularBasis i)
          (angularEmbedding (nativeHalfHighFullInverseEntranceEnergy hκ0 hκ1 V hV F)) =
        nativeHalfHighFullInverse hκ0 hκ1 V hV F 0 i := by
    rw [nativeHalfHighFullInverseEntranceEnergy_embedding,
      ← HilbertBasis.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply]
  rw [nativeHighProjection, nativeAngularProjection_coefficient]
  by_cases hi : 6 ≤ angularEigenvalue i
  · rw [if_pos hi]
  · rw [if_neg hi]
    exact (hcoeff i |>.trans
      (nativeHalfHighFullInverse_low_zero hκ0 hκ1 V hV F i (lt_of_not_ge hi) 0)).symm

/-- The original native forced Dirichlet curve is exactly the original
full-line physical term minus the same-potential Poisson correction of
its actual H1 entrance value. -/
theorem nativeHalfHighDirichletPhysical_eq_full_sub
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ) (ht : 0 ≤ t) :
    nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t =
      angularBasis.repr.symm
          (Real.exp (-2 * t) • nativeHalfHighFullInverse hκ0 hκ1 V hV F t) -
        nativeHalfHighPotentialPhysical hκ0 hκ1 V hV hV0
          (nativeHalfHighFullInverseEntranceEnergy hκ0 hκ1 V hV F) t := by
  have hb : angularBasis.repr
      (nativeHighProjection
        (angularEmbedding (nativeHalfHighFullInverseEntranceEnergy hκ0 hκ1 V hV F))) =
      nativeHalfHighFullInverse hκ0 hκ1 V hV F 0 := by
    rw [nativeHalfHighFullInverseEntranceEnergy_high,
      nativeHalfHighFullInverseEntranceEnergy_embedding, LinearIsometryEquiv.apply_symm_apply]
  rw [nativeHalfHighDirichletPhysical, nativeHalfHighDirichletCLM_apply,
    spectralHalfPotentialDirichletCLM_apply]
  change Real.exp (-2 * t) • angularBasis.repr.symm
    (nativeHalfHighFullInverse hκ0 hκ1 V hV F (t.toNNReal : ℝ) -
      spectralHalfPotentialPoissonCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
        hκ0 hκ1 V hV hV0 (nativeHalfHighFullInverse hκ0 hκ1 V hV F 0) t.toNNReal) = _
  rw [Real.coe_toNNReal t ht, map_sub, smul_sub,
    nativeHalfHighPotentialPhysical, nativeHalfHighPotentialPoissonCLM_apply, hb, map_smul]

/-- A continuous actual AngularL2 derivative candidate for the original
forced curve, formed from the two already proved strong derivatives. -/
def nativeHalfHighDirichletPhysicalDerivative
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ) : AngularL2 :=
  angularBasis.repr.symm (Real.exp (-2 * t) •
    spectralFirstDerivativeConvolution nativeAngularRate (by norm_num) nativeAngularRate_lower
      (-2) (nativeHalfHighFullSource F - V • nativeHalfHighFullInverse hκ0 hκ1 V hV F) t) -
    nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0
      (nativeHalfHighFullInverseEntranceEnergy hκ0 hκ1 V hV F) t

theorem nativeHalfHighDirichletPhysicalDerivative_continuous (F : ℝ≥0 →ᵇ AngularL2) :
    Continuous (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F) := by
  apply Continuous.sub _
    (nativeHalfHighPotentialPhysicalDerivative_continuous hκ0 hκ1 V hV hV0
      (nativeHalfHighFullInverseEntranceEnergy hκ0 hκ1 V hV F))
  exact angularBasis.repr.symm.continuous.comp
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      (spectralFirstDerivativeConvolution_continuous nativeAngularRate (by norm_num)
        nativeAngularRate_lower (by norm_num : |(-2 : ℝ)| < (5 / 2 : ℝ)) _))

/-- Genuine strong differentiation on the closed half-line, including
the right derivative at the actual zero Dirichlet entrance. -/
theorem nativeHalfHighDirichletPhysical_hasDerivWithinAt
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F)
      (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t) (Ici 0) t := by
  let A := angularBasis.repr.symm.toLinearIsometry.toContinuousLinearMap
  have hfull := spectralIntegralPotentialInverse_weighted_hasDerivAt nativeAngularRate
    (by norm_num : (0 : ℝ) < 5 / 2) nativeAngularRate_lower
    (by norm_num : |(-2 : ℝ)| < (5 / 2 : ℝ)) hκ0 hκ1 V hV (nativeHalfHighFullSource F) t
  have hd := (A.hasFDerivAt.comp_hasDerivAt t hfull).hasDerivWithinAt.sub
    (nativeHalfHighPotentialPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0
      (nativeHalfHighFullInverseEntranceEnergy hκ0 hκ1 V hV F) t ht)
  apply hd.congr_of_mem _ ht
  intro s hs
  exact nativeHalfHighDirichletPhysical_eq_full_sub hκ0 hκ1 V hV hV0 F s hs

theorem nativeHalfHighDirichletPhysical_hasDerivAt
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F)
      (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t) t :=
  (nativeHalfHighDirichletPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 F t ht.le).hasDerivAt
    (Ici_mem_nhds ht)

private theorem nativeHalfHighFullInverse_effective_source_norm_le
    (F : ℝ≥0 →ᵇ AngularL2) :
    ‖nativeHalfHighFullSource F - V • nativeHalfHighFullInverse hκ0 hκ1 V hV F‖ ≤
      (1 + (4 / 9 : ℝ) * ‖V‖ / (1 - κ)) * ‖F‖ := by
  calc
    _ ≤ ‖nativeHalfHighFullSource F‖ + ‖V • nativeHalfHighFullInverse hκ0 hκ1 V hV F‖ :=
      norm_sub_le _ _
    _ ≤ ‖F‖ + ‖V‖ * (((4 / 9 : ℝ) / (1 - κ)) * ‖F‖) := add_le_add
      (nativeHalfHighFullSource_norm_le F)
      ((norm_smul_le V _).trans (mul_le_mul_of_nonneg_left
        (nativeHalfHighFullInverse_norm_le hκ0 hκ1 V hV F) (norm_nonneg V)))
    _ = _ := by ring

/-- An explicit weighted strong-derivative bound for the original
forced field.  The constant is fixed before the source and time. -/
theorem nativeHalfHighDirichletPhysicalDerivative_weighted_norm_le
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (2 * t) * ‖nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t‖ ≤
      ((10 / 9 : ℝ) * (1 + (4 / 9 : ℝ) * ‖V‖ / (1 - κ)) +
        (1 + (10 / 9 : ℝ) * ‖V‖ / (1 - κ)) *
          ((20 / 9 : ℝ) * (1 + (4 / 9 : ℝ) * ‖V‖ / (1 - κ)))) * ‖F‖ := by
  let G := nativeHalfHighFullSource F - V • nativeHalfHighFullInverse hκ0 hκ1 V hV F
  let b := nativeHalfHighFullInverseEntranceEnergy hκ0 hκ1 V hV F
  have hκ : 0 < 1 - κ := sub_pos.mpr hκ1
  have he : Real.exp (2 * t) * Real.exp (-2 * t) = 1 := by
    rw [← Real.exp_add, show 2 * t + -2 * t = 0 by ring, Real.exp_zero]
  have hD : ‖spectralFirstDerivativeConvolution nativeAngularRate (by norm_num)
      nativeAngularRate_lower (-2) G t‖ ≤ (10 / 9 : ℝ) * ‖G‖ := by
    convert spectralFirstDerivativeConvolution_norm_le nativeAngularRate (by norm_num)
      nativeAngularRate_lower (by norm_num : |(-2 : ℝ)| < (5 / 2 : ℝ)) G t using 1 <;>
      norm_num <;> ring
  have hsource : ‖G‖ ≤ (1 + (4 / 9 : ℝ) * ‖V‖ / (1 - κ)) * ‖F‖ :=
    nativeHalfHighFullInverse_effective_source_norm_le hκ0 hκ1 V hV F
  have hb : ‖b‖ ≤ (20 / 9 : ℝ) * (1 + (4 / 9 : ℝ) * ‖V‖ / (1 - κ)) * ‖F‖ :=
    nativeHalfHighFullInverseEntranceEnergy_norm_le hκ0 hκ1 V hV F
  calc
    _ ≤ Real.exp (2 * t) *
        (‖angularBasis.repr.symm (Real.exp (-2 * t) •
          spectralFirstDerivativeConvolution nativeAngularRate (by norm_num)
            nativeAngularRate_lower (-2) G t)‖ +
          ‖nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 b t‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.exp_pos _).le
    _ = ‖spectralFirstDerivativeConvolution nativeAngularRate (by norm_num)
        nativeAngularRate_lower (-2) G t‖ + Real.exp (2 * t) *
          ‖nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 b t‖ := by
      rw [mul_add, LinearIsometryEquiv.norm_map, norm_smul,
        Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc, he, one_mul]
    _ ≤ (10 / 9 : ℝ) * ((1 + (4 / 9 : ℝ) * ‖V‖ / (1 - κ)) * ‖F‖) +
        (1 + (10 / 9 : ℝ) * ‖V‖ / (1 - κ)) *
          (((20 / 9 : ℝ) * (1 + (4 / 9 : ℝ) * ‖V‖ / (1 - κ))) * ‖F‖) :=
      add_le_add (hD.trans (mul_le_mul_of_nonneg_left hsource (by norm_num)))
        (((nativeHalfHighPotentialPhysical_weighted_cauchy hκ0 hκ1 V hV hV0 b t ht).2).trans
          (mul_le_mul_of_nonneg_left hb (by positivity)))
    _ = _ := by ring

/-- The new strong derivative decays for every fixed original source. -/
theorem nativeHalfHighDirichletPhysicalDerivative_tendsto_zero
    (F : ℝ≥0 →ᵇ AngularL2) :
    Tendsto (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F) atTop (𝓝 0) :=
  halfEnd_tendsto_zero_of_expTwo_bound _ _
    (nativeHalfHighDirichletPhysicalDerivative_weighted_norm_le hκ0 hκ1 V hV hV0 F)

/-- Each coordinate of the produced strong derivative obeys the true
native eigenvalue equation of the same original forced field. -/
theorem nativeHalfHighDirichletPhysicalDerivative_coefficient_equation
    (F : ℝ≥0 →ᵇ AngularL2) (i : AngularIndex) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => inner ℝ (angularBasis i)
      (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F s))
      ((angularEigenvalue i + 1 / 4 - V t) * inner ℝ (angularBasis i)
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t) +
          Real.exp (-2 * t) * inner ℝ (angularBasis i) (nativeHighProjection (F t.toNNReal))) t := by
  let ev : AngularL2 →L[ℝ] ℝ := innerSL ℝ (angularBasis i)
  have heq : (fun s => inner ℝ (angularBasis i)
      (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F s)) =ᶠ[𝓝 t]
      deriv (fun s => inner ℝ (angularBasis i)
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F s)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (ev.hasFDerivAt.comp_hasDerivAt s
      (nativeHalfHighDirichletPhysical_hasDerivAt hκ0 hκ1 V hV hV0 F s hs)).deriv.symm
  exact (nativeHalfHighDirichletPhysical_coefficient_equation
    hκ0 hκ1 V hV hV0 F i t ht).congr_of_eventuallyEq heq

#print axioms nativeHalfHighFullInverseEntranceEnergy_embedding
#print axioms nativeHalfHighFullInverseEntranceEnergy_high
#print axioms nativeHalfHighDirichletPhysical_eq_full_sub
#print axioms nativeHalfHighDirichletPhysical_hasDerivWithinAt
#print axioms nativeHalfHighDirichletPhysicalDerivative_weighted_norm_le
#print axioms nativeHalfHighDirichletPhysicalDerivative_coefficient_equation

end Yamabe3.Analysis.Delaunay
