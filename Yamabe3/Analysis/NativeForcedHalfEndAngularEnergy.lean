import Yamabe3.Analysis.NativeForcedHalfEndStrongDerivative

/-!
# The same forced half-end in the actual angular H1 space

The free weighted Poisson curve is constructed through the already proved
Hilbert basis of the native H1 completion.  Its rates are the actual
nonnegative numbers `nativeAngularRate - 2`.  Combining this curve with
the same root-convolution representative of the original potential
correction produces the H1 representative of the original Poisson map.

The forced H1 curve then uses the original full-line inverse and its
already produced H1 entrance value.  Its actual L2 embedding is exactly
the original native Dirichlet curve, at every nonnegative time.  The
physical representative is continuous in H1, has zero entrance, and
decays in that norm.  These are produced regularity statements, with no
H1 hypothesis on the source or on a separately supplied entrance datum.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

open SphereSpectrum Poincare.Analysis.Dirichlet.Spectral

private def nativeWeightedEnergyRate (i : AngularIndex) : ℝ≥0 :=
  ⟨nativeAngularRate i - 2, by have := nativeAngularRate_lower i; linarith⟩

/-- The actual weighted free Poisson evolution in the native H1 space.
The same clipped rates occur in the original full-line free extension. -/
def nativeWeightedFreePoissonEnergy (t : ℝ≥0) : AngularH1 →L[ℝ] AngularH1 :=
  heat angularEnergyBasis nativeWeightedEnergyRate t

theorem nativeWeightedFreePoissonEnergy_embedding_coefficient
    (b : AngularH1) (t : ℝ≥0) (i : AngularIndex) :
    inner ℝ (angularBasis i) (angularEmbedding (nativeWeightedFreePoissonEnergy t b)) =
      Real.exp ((2 - nativeAngularRate i) * (t : ℝ)) *
        inner ℝ (angularBasis i) (angularEmbedding b) := by
  have h := heat_repr angularEnergyBasis nativeWeightedEnergyRate t b i
  rw [angularEnergyBasis_repr, angularEnergyBasis_repr] at h
  change angularEnergyWeight i * inner ℝ (angularBasis i)
      (angularEmbedding (nativeWeightedFreePoissonEnergy t b)) =
    Real.exp (-(nativeAngularRate i - 2) * (t : ℝ)) *
      (angularEnergyWeight i * inner ℝ (angularBasis i) (angularEmbedding b)) at h
  rw [show -(nativeAngularRate i - 2) = 2 - nativeAngularRate i by ring] at h
  apply mul_left_cancel₀ (angularEnergyWeight_pos i).ne'
  calc
    _ = Real.exp ((2 - nativeAngularRate i) * (t : ℝ)) *
        (angularEnergyWeight i * inner ℝ (angularBasis i) (angularEmbedding b)) := h
    _ = _ := by ring

theorem nativeWeightedFreePoissonEnergy_embedding (b : AngularH1) (t : ℝ≥0) :
    angularEmbedding (nativeWeightedFreePoissonEnergy t b) =
      angularBasis.repr.symm (spectralFullBoundaryPoissonCLM nativeAngularRate
        (by norm_num) nativeAngularRate_lower
        (angularBasis.repr (angularEmbedding b)) (t : ℝ)) := by
  apply angularBasis.repr.injective
  ext i
  rw [HilbertBasis.repr_apply_apply, nativeWeightedFreePoissonEnergy_embedding_coefficient,
    LinearIsometryEquiv.apply_symm_apply, spectralFullBoundaryPoissonCLM_coordinate,
    HilbertBasis.repr_apply_apply, abs_of_nonneg t.coe_nonneg]
  rw [show (2 - nativeAngularRate i) * (t : ℝ) =
    2 * (t : ℝ) - nativeAngularRate i * (t : ℝ) by ring]

theorem nativeWeightedFreePoissonEnergy_continuous (b : AngularH1) :
    Continuous (fun t : ℝ≥0 => nativeWeightedFreePoissonEnergy t b) :=
  continuous_heat angularEnergyBasis nativeWeightedEnergyRate b

theorem nativeWeightedFreePoissonEnergy_norm_le (b : AngularH1) (t : ℝ≥0) :
    ‖nativeWeightedFreePoissonEnergy t b‖ ≤ ‖b‖ :=
  norm_heat_apply_le angularEnergyBasis nativeWeightedEnergyRate t b

/-- A numerical abbreviation for the already proved root-energy bound. -/
def nativeHalfHighEnergySourceBound (κ : ℝ) (V : ℝ →ᵇ ℝ) : ℝ :=
  (20 / 9 : ℝ) * (1 + (4 / 9 : ℝ) * ‖V‖ / (1 - κ))

theorem nativeHalfHighEnergySourceBound_nonneg
    {κ : ℝ} (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ) :
    0 ≤ nativeHalfHighEnergySourceBound κ V := by
  have hκ : 0 < 1 - κ := sub_pos.mpr hκ1
  unfold nativeHalfHighEnergySourceBound
  positivity

/-- The bound for the actual forced energy curve. -/
def nativeHalfHighDirichletEnergyBound (κ : ℝ) (V : ℝ →ᵇ ℝ) : ℝ :=
  nativeHalfHighEnergySourceBound κ V +
    (1 + nativeHalfHighEnergySourceBound κ V * ‖V‖) * nativeHalfHighEnergySourceBound κ V

theorem nativeHalfHighDirichletEnergyBound_nonneg
    {κ : ℝ} (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ) :
    0 ≤ nativeHalfHighDirichletEnergyBound κ V := by
  have hE := nativeHalfHighEnergySourceBound_nonneg hκ1 V
  unfold nativeHalfHighDirichletEnergyBound
  positivity

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

private def nativeHalfEnergyCorrectionSource (b : AngularH1) :
    ℝ →ᵇ SpectralSpace AngularIndex :=
  V • spectralFullBoundaryPoissonCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
    (angularBasis.repr (angularEmbedding (nativeHighEnergyEntranceCLM hκ0 hκ1 V hV hV0 b)))

private theorem nativeHalfEnergyCorrectionSource_norm_le (b : AngularH1) :
    ‖nativeHalfEnergyCorrectionSource hκ0 hκ1 V hV hV0 b‖ ≤ ‖V‖ * ‖b‖ := by
  have hb : ‖angularBasis.repr
      (angularEmbedding (nativeHighEnergyEntranceCLM hκ0 hκ1 V hV hV0 b))‖ ≤ ‖b‖ := by
    rw [LinearIsometryEquiv.norm_map]
    exact (PoincareMT.LeviCivitaData.Dirichlet.norm_toDomainL2_le _).trans
      (nativeHighEnergyEntranceCLM_norm_le hκ0 hκ1 V hV hV0 b)
  exact (norm_smul_le V _).trans (mul_le_mul_of_nonneg_left
    ((spectralFullBoundaryPoissonCLM_apply_norm_le nativeAngularRate (by norm_num)
      nativeAngularRate_lower _).trans hb) (norm_nonneg V))

/-- The actual H1 representative of the same potential Poisson curve. -/
def nativeHalfHighPotentialPoissonEnergy (b : AngularH1) (t : ℝ≥0) : AngularH1 :=
  nativeWeightedFreePoissonEnergy t (nativeHighEnergyEntranceCLM hκ0 hκ1 V hV hV0 b) -
    nativeIntegralPotentialEnergy hκ0 hκ1 V hV
      (nativeHalfEnergyCorrectionSource hκ0 hκ1 V hV hV0 b) (t : ℝ)

theorem nativeHalfHighPotentialPoissonEnergy_embedding (b : AngularH1) (t : ℝ≥0) :
    angularEmbedding (nativeHalfHighPotentialPoissonEnergy hκ0 hκ1 V hV hV0 b t) =
      nativeHalfHighPotentialPoissonCLM hκ0 hκ1 V hV hV0 b t := by
  rw [nativeHalfHighPotentialPoissonEnergy, map_sub,
    nativeWeightedFreePoissonEnergy_embedding, nativeIntegralPotentialEnergy_embedding,
    nativeHalfHighPotentialPoissonCLM_apply, spectralHalfPotentialPoissonCLM_apply,
    ← nativeHighEnergyEntranceCLM_embedding_repr hκ0 hκ1 V hV hV0 b, map_sub]
  rfl

theorem nativeHalfHighPotentialPoissonEnergy_continuous (b : AngularH1) :
    Continuous (nativeHalfHighPotentialPoissonEnergy hκ0 hκ1 V hV hV0 b) :=
  (nativeWeightedFreePoissonEnergy_continuous _).sub
    ((nativeIntegralPotentialEnergy_continuous hκ0 hκ1 V hV _).comp continuous_subtype_val)

theorem nativeHalfHighPotentialPoissonEnergy_norm_le (b : AngularH1) (t : ℝ≥0) :
    ‖nativeHalfHighPotentialPoissonEnergy hκ0 hκ1 V hV hV0 b t‖ ≤
      (1 + nativeHalfHighEnergySourceBound κ V * ‖V‖) * ‖b‖ := by
  have hE := nativeHalfHighEnergySourceBound_nonneg hκ1 V
  calc
    _ ≤ ‖nativeWeightedFreePoissonEnergy t
          (nativeHighEnergyEntranceCLM hκ0 hκ1 V hV hV0 b)‖ +
        ‖nativeIntegralPotentialEnergy hκ0 hκ1 V hV
          (nativeHalfEnergyCorrectionSource hκ0 hκ1 V hV hV0 b) (t : ℝ)‖ := norm_sub_le _ _
    _ ≤ ‖b‖ + nativeHalfHighEnergySourceBound κ V *
        ‖nativeHalfEnergyCorrectionSource hκ0 hκ1 V hV hV0 b‖ := add_le_add
      ((nativeWeightedFreePoissonEnergy_norm_le _ t).trans
        (nativeHighEnergyEntranceCLM_norm_le hκ0 hκ1 V hV hV0 b))
      (nativeIntegralPotentialEnergy_norm_le hκ0 hκ1 V hV _ (t : ℝ))
    _ ≤ ‖b‖ + nativeHalfHighEnergySourceBound κ V * (‖V‖ * ‖b‖) := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left
        (nativeHalfEnergyCorrectionSource_norm_le hκ0 hκ1 V hV hV0 b) hE)
    _ = _ := by ring

theorem nativeHalfHighPotentialPoissonEnergy_zero (b : AngularH1) :
    nativeHalfHighPotentialPoissonEnergy hκ0 hκ1 V hV hV0 b 0 =
      nativeHighEnergyProjectionCLM b := by
  apply angularEmbedding_injective
  rw [nativeHalfHighPotentialPoissonEnergy_embedding, nativeHalfHighPotentialPoissonCLM_zero]

private def nativeHalfHighDirichletEnergyValue
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ≥0) : AngularH1 :=
  nativeIntegralPotentialEnergy hκ0 hκ1 V hV (nativeHalfHighFullSource F) (t : ℝ) -
    nativeHalfHighPotentialPoissonEnergy hκ0 hκ1 V hV hV0
      (nativeHalfHighFullInverseEntranceEnergy hκ0 hκ1 V hV F) t

private theorem nativeHalfHighDirichletEnergyValue_continuous
    (F : ℝ≥0 →ᵇ AngularL2) :
    Continuous (nativeHalfHighDirichletEnergyValue hκ0 hκ1 V hV hV0 F) :=
  ((nativeIntegralPotentialEnergy_continuous hκ0 hκ1 V hV _).comp
    continuous_subtype_val).sub (nativeHalfHighPotentialPoissonEnergy_continuous
      hκ0 hκ1 V hV hV0 _)

private theorem nativeHalfHighDirichletEnergyValue_norm_le
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ≥0) :
    ‖nativeHalfHighDirichletEnergyValue hκ0 hκ1 V hV hV0 F t‖ ≤
      nativeHalfHighDirichletEnergyBound κ V * ‖F‖ := by
  have hE := nativeHalfHighEnergySourceBound_nonneg hκ1 V
  have hP : 0 ≤ 1 + nativeHalfHighEnergySourceBound κ V * ‖V‖ := by positivity
  have hA : ‖nativeHalfHighFullInverseEntranceEnergy hκ0 hκ1 V hV F‖ ≤
      nativeHalfHighEnergySourceBound κ V * ‖F‖ := by
    simpa only [nativeHalfHighEnergySourceBound] using
      nativeHalfHighFullInverseEntranceEnergy_norm_le hκ0 hκ1 V hV F
  calc
    _ ≤ ‖nativeIntegralPotentialEnergy hκ0 hκ1 V hV
          (nativeHalfHighFullSource F) (t : ℝ)‖ +
        ‖nativeHalfHighPotentialPoissonEnergy hκ0 hκ1 V hV hV0
          (nativeHalfHighFullInverseEntranceEnergy hκ0 hκ1 V hV F) t‖ := norm_sub_le _ _
    _ ≤ nativeHalfHighEnergySourceBound κ V * ‖F‖ +
        (1 + nativeHalfHighEnergySourceBound κ V * ‖V‖) *
          ‖nativeHalfHighFullInverseEntranceEnergy hκ0 hκ1 V hV F‖ := add_le_add
      ((nativeIntegralPotentialEnergy_norm_le hκ0 hκ1 V hV _ (t : ℝ)).trans
        (mul_le_mul_of_nonneg_left (nativeHalfHighFullSource_norm_le F) hE))
      (nativeHalfHighPotentialPoissonEnergy_norm_le hκ0 hκ1 V hV hV0 _ t)
    _ ≤ nativeHalfHighEnergySourceBound κ V * ‖F‖ +
        (1 + nativeHalfHighEnergySourceBound κ V * ‖V‖) *
          (nativeHalfHighEnergySourceBound κ V * ‖F‖) := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hA hP)
    _ = _ := by unfold nativeHalfHighDirichletEnergyBound; ring

/-- A genuine bounded continuous H1 curve produced from the L2 source. -/
def nativeHalfHighDirichletEnergy (F : ℝ≥0 →ᵇ AngularL2) : ℝ≥0 →ᵇ AngularH1 :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (nativeHalfHighDirichletEnergyValue hκ0 hκ1 V hV hV0 F)
    (nativeHalfHighDirichletEnergyValue_continuous hκ0 hκ1 V hV hV0 F)
    (nativeHalfHighDirichletEnergyBound κ V * ‖F‖)
    (nativeHalfHighDirichletEnergyValue_norm_le hκ0 hκ1 V hV hV0 F)

theorem nativeHalfHighDirichletEnergy_embedding (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ≥0) :
    angularEmbedding (nativeHalfHighDirichletEnergy hκ0 hκ1 V hV hV0 F t) =
      nativeHalfHighDirichletCLM hκ0 hκ1 V hV hV0 F t := by
  have hb : angularBasis.repr
      (nativeHighProjection
        (angularEmbedding (nativeHalfHighFullInverseEntranceEnergy hκ0 hκ1 V hV F))) =
      nativeHalfHighFullInverse hκ0 hκ1 V hV F 0 := by
    rw [nativeHalfHighFullInverseEntranceEnergy_high,
      nativeHalfHighFullInverseEntranceEnergy_embedding, LinearIsometryEquiv.apply_symm_apply]
  change angularEmbedding
    (nativeIntegralPotentialEnergy hκ0 hκ1 V hV (nativeHalfHighFullSource F) (t : ℝ) -
      nativeHalfHighPotentialPoissonEnergy hκ0 hκ1 V hV hV0
        (nativeHalfHighFullInverseEntranceEnergy hκ0 hκ1 V hV F) t) = _
  rw [map_sub, nativeIntegralPotentialEnergy_embedding,
    nativeHalfHighPotentialPoissonEnergy_embedding, nativeHalfHighPotentialPoissonCLM_apply,
    hb, nativeHalfHighDirichletCLM_apply, spectralHalfPotentialDirichletCLM_apply, map_sub]
  rfl

theorem nativeHalfHighDirichletEnergy_norm_le (F : ℝ≥0 →ᵇ AngularL2) :
    ‖nativeHalfHighDirichletEnergy hκ0 hκ1 V hV hV0 F‖ ≤
      nativeHalfHighDirichletEnergyBound κ V * ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (nativeHalfHighDirichletEnergyBound_nonneg hκ1 V) (norm_nonneg F))).mpr
  exact nativeHalfHighDirichletEnergyValue_norm_le hκ0 hκ1 V hV hV0 F

theorem nativeHalfHighDirichletEnergy_zero (F : ℝ≥0 →ᵇ AngularL2) :
    nativeHalfHighDirichletEnergy hκ0 hκ1 V hV hV0 F 0 = 0 := by
  apply angularEmbedding_injective
  rw [nativeHalfHighDirichletEnergy_embedding, nativeHalfHighDirichletCLM_zero, map_zero]

/-- The actual weighted Dirichlet solution is a bounded linear H1-valued
source operator; linearity follows through its faithful original L2 image. -/
def nativeHalfHighDirichletEnergyCLM :
    (ℝ≥0 →ᵇ AngularL2) →L[ℝ] (ℝ≥0 →ᵇ AngularH1) :=
  ({ toFun := nativeHalfHighDirichletEnergy hκ0 hκ1 V hV hV0
     map_add' := by
       intro F G
       apply BoundedContinuousFunction.ext
       intro t
       apply angularEmbedding_injective
       simp only [BoundedContinuousFunction.add_apply, map_add,
         nativeHalfHighDirichletEnergy_embedding]
     map_smul' := by
       intro c F
       apply BoundedContinuousFunction.ext
       intro t
       apply angularEmbedding_injective
       simp only [BoundedContinuousFunction.smul_apply, map_smul, RingHom.id_apply,
         nativeHalfHighDirichletEnergy_embedding] } :
      (ℝ≥0 →ᵇ AngularL2) →ₗ[ℝ] (ℝ≥0 →ᵇ AngularH1)).mkContinuous
    (nativeHalfHighDirichletEnergyBound κ V)
    (nativeHalfHighDirichletEnergy_norm_le hκ0 hκ1 V hV hV0)

theorem nativeHalfHighDirichletEnergyCLM_apply (F : ℝ≥0 →ᵇ AngularL2) :
    nativeHalfHighDirichletEnergyCLM hκ0 hκ1 V hV hV0 F =
      nativeHalfHighDirichletEnergy hκ0 hκ1 V hV hV0 F := rfl

theorem nativeHalfHighDirichletEnergyCLM_source_difference
    (F G : ℝ≥0 →ᵇ AngularL2) :
    ‖nativeHalfHighDirichletEnergyCLM hκ0 hκ1 V hV hV0 F -
      nativeHalfHighDirichletEnergyCLM hκ0 hκ1 V hV hV0 G‖ ≤
      nativeHalfHighDirichletEnergyBound κ V * ‖F - G‖ := by
  rw [← map_sub]
  exact nativeHalfHighDirichletEnergy_norm_le hκ0 hκ1 V hV hV0 (F - G)

/-- Removing the original weight from the actual energy representative. -/
def nativeHalfHighDirichletPhysicalEnergy (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ) : AngularH1 :=
  Real.exp (-2 * t) • nativeHalfHighDirichletEnergy hκ0 hκ1 V hV hV0 F t.toNNReal

theorem nativeHalfHighDirichletPhysicalEnergy_embedding
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ) :
    angularEmbedding (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F t) =
      nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t := by
  rw [nativeHalfHighDirichletPhysicalEnergy, map_smul, nativeHalfHighDirichletEnergy_embedding]
  rfl

theorem nativeHalfHighDirichletPhysicalEnergy_continuous (F : ℝ≥0 →ᵇ AngularL2) :
    Continuous (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    ((nativeHalfHighDirichletEnergy hκ0 hκ1 V hV hV0 F).continuous.comp continuous_real_toNNReal)

theorem nativeHalfHighDirichletPhysicalEnergy_zero_of_nonpos
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ) (ht : t ≤ 0) :
    nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F t = 0 := by
  rw [nativeHalfHighDirichletPhysicalEnergy, Real.toNNReal_of_nonpos ht,
    nativeHalfHighDirichletEnergy_zero, smul_zero]

theorem nativeHalfHighDirichletPhysicalEnergy_weighted_norm_le
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ) :
    Real.exp (2 * t) * ‖nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F t‖ ≤
      nativeHalfHighDirichletEnergyBound κ V * ‖F‖ := by
  have he : Real.exp (2 * t) * Real.exp (-2 * t) = 1 := by
    rw [← Real.exp_add, show 2 * t + -2 * t = 0 by ring, Real.exp_zero]
  rw [nativeHalfHighDirichletPhysicalEnergy, norm_smul,
    Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc, he, one_mul]
  exact ((nativeHalfHighDirichletEnergy hκ0 hκ1 V hV hV0 F).norm_coe_le_norm _).trans
    (nativeHalfHighDirichletEnergy_norm_le hκ0 hκ1 V hV hV0 F)

theorem nativeHalfHighDirichletPhysicalEnergy_tendsto_zero (F : ℝ≥0 →ᵇ AngularL2) :
    Tendsto (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F) atTop (𝓝 0) :=
  halfEnd_tendsto_zero_of_expTwo_bound _ _
    (fun t _ht => nativeHalfHighDirichletPhysicalEnergy_weighted_norm_le hκ0 hκ1 V hV hV0 F t)

#print axioms nativeWeightedFreePoissonEnergy_embedding
#print axioms nativeHalfHighPotentialPoissonEnergy_embedding
#print axioms nativeHalfHighPotentialPoissonEnergy_continuous
#print axioms nativeHalfHighDirichletEnergy_embedding
#print axioms nativeHalfHighDirichletEnergyCLM
#print axioms nativeHalfHighDirichletEnergyCLM_source_difference
#print axioms nativeHalfHighDirichletPhysicalEnergy_embedding
#print axioms nativeHalfHighDirichletPhysicalEnergy_tendsto_zero

end Yamabe3.Analysis.Delaunay
