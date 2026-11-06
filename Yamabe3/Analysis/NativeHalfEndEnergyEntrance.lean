import Yamabe3.Analysis.SpectralHalfEndPotentialEntrance
import Yamabe3.Analysis.Sphere.NativeSphereEnergyBasis
import Yamabe3.Analysis.NativeHighFreePoisson

/-!
# Actual high half-end entrance data in the native H1 completion

The reciprocal entrance diagonal already constructed from the same R_V
acts through the genuine energy Hilbert basis. Its output is a literal
native AngularH1 element with norm at most the original datum, and its
L2 embedding is exactly the auxiliary entrance vector used by the actual
half-end solution. The high projection is likewise constructed inside
that same H1 completion. No arbitrary-L2 H1 lifting is asserted.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

open SphereSpectrum

/-- The actual high projection on the genuine round-sphere H1 space. -/
def nativeHighEnergyProjectionCLM : AngularH1 →L[ℝ] AngularH1 :=
  nativeAngularEnergyDiagonal (fun i => if 6 ≤ angularEigenvalue i then (1 : ℝ) else 0)
    zero_le_one (fun i => by
      classical
      split_ifs <;> norm_num)

theorem nativeHighEnergyProjectionCLM_embedding (b : AngularH1) :
    angularEmbedding (nativeHighEnergyProjectionCLM b) = nativeHighProjection (angularEmbedding b) := by
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply]
  rw [nativeHighEnergyProjectionCLM, nativeAngularEnergyDiagonal_embedding_coefficient,
    nativeHighProjection, nativeAngularProjection_coefficient]
  split_ifs <;> simp

theorem nativeHighEnergyProjectionCLM_norm_le (b : AngularH1) :
    ‖nativeHighEnergyProjectionCLM b‖ ≤ ‖b‖ := by
  simpa only [nativeHighEnergyProjectionCLM, one_mul] using nativeAngularEnergyDiagonal_apply_norm_le
    (fun i => if 6 ≤ angularEigenvalue i then (1 : ℝ) else 0)
    zero_le_one (fun i => by
      classical
      split_ifs <;> norm_num) b

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

private def nativeHighEntranceMultiplier (i : AngularIndex) : ℝ :=
  if 6 ≤ angularEigenvalue i then
    (1 - spectralHalfBoundaryCorrectionCoefficient nativeAngularRate (by norm_num)
      nativeAngularRate_lower hκ0 hκ1 V hV i)⁻¹
  else 0

include hV0 in
private theorem nativeHighEntranceMultiplier_bound (i : AngularIndex) :
    |nativeHighEntranceMultiplier hκ0 hκ1 V hV i| ≤ 1 := by
  unfold nativeHighEntranceMultiplier
  split_ifs
  · have hn := spectralHalfBoundaryCorrectionCoefficient_nonpos nativeAngularRate
      (by norm_num) nativeAngularRate_lower hκ0 hκ1 V hV hV0 i
    have hd : 1 ≤ 1 - spectralHalfBoundaryCorrectionCoefficient nativeAngularRate
        (by norm_num) nativeAngularRate_lower hκ0 hκ1 V hV i := by linarith
    rw [abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hd)), ← one_div]
    exact (one_div_le_one_div_of_le zero_lt_one hd).trans_eq (by norm_num)
  · norm_num

/-- This is the true H1 auxiliary entrance datum selected by the actual
potential correction. Its L2 image is proved equal to the constructed
spectral reciprocal, rather than supplied as a separate certificate. -/
def nativeHighEnergyEntranceCLM : AngularH1 →L[ℝ] AngularH1 :=
  nativeAngularEnergyDiagonal (nativeHighEntranceMultiplier hκ0 hκ1 V hV) zero_le_one
    (nativeHighEntranceMultiplier_bound hκ0 hκ1 V hV hV0)

theorem nativeHighEnergyEntranceCLM_norm_le (b : AngularH1) :
    ‖nativeHighEnergyEntranceCLM hκ0 hκ1 V hV hV0 b‖ ≤ ‖b‖ := by
  simpa only [nativeHighEnergyEntranceCLM, one_mul] using nativeAngularEnergyDiagonal_apply_norm_le
    (nativeHighEntranceMultiplier hκ0 hκ1 V hV) zero_le_one
    (nativeHighEntranceMultiplier_bound hκ0 hκ1 V hV hV0) b

theorem nativeHighEnergyEntranceCLM_embedding_repr (b : AngularH1) :
    angularBasis.repr (angularEmbedding (nativeHighEnergyEntranceCLM hκ0 hκ1 V hV hV0 b)) =
      spectralHalfEntranceInverseCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
        hκ0 hκ1 V hV hV0 (angularBasis.repr (nativeHighProjection (angularEmbedding b))) := by
  ext i
  rw [HilbertBasis.repr_apply_apply, nativeHighEnergyEntranceCLM,
    nativeAngularEnergyDiagonal_embedding_coefficient, spectralHalfEntranceInverseCLM_coordinate,
    HilbertBasis.repr_apply_apply, nativeHighProjection, nativeAngularProjection_coefficient]
  unfold nativeHighEntranceMultiplier
  split_ifs <;> simp

theorem nativeHighEnergyEntranceCLM_embedding_high (b : AngularH1) :
    nativeHighProjection (angularEmbedding (nativeHighEnergyEntranceCLM hκ0 hκ1 V hV hV0 b)) =
      angularEmbedding (nativeHighEnergyEntranceCLM hκ0 hκ1 V hV hV0 b) := by
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply]
  rw [nativeHighProjection, nativeAngularProjection_coefficient,
    nativeHighEnergyEntranceCLM, nativeAngularEnergyDiagonal_embedding_coefficient]
  unfold nativeHighEntranceMultiplier
  split_ifs <;> simp

/-- Native angular synthesis of the actual constructed half-end curve,
with input in the genuine native H1 boundary space. -/
def nativeHalfHighPotentialPoissonCLM : AngularH1 →L[ℝ] (ℝ≥0 →ᵇ AngularL2) :=
  (angularBasis.repr.symm.toLinearIsometry.toContinuousLinearMap.compLeftContinuousBounded ℝ≥0).comp
    ((spectralHalfPotentialPoissonCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
      hκ0 hκ1 V hV hV0).comp
        (angularBasis.repr.toLinearIsometry.toContinuousLinearMap.comp
          (nativeHighProjection.comp angularEmbedding)))

theorem nativeHalfHighPotentialPoissonCLM_apply (b : AngularH1) (t : ℝ≥0) :
    nativeHalfHighPotentialPoissonCLM hκ0 hκ1 V hV hV0 b t =
      angularBasis.repr.symm (spectralHalfPotentialPoissonCLM nativeAngularRate
        (by norm_num) nativeAngularRate_lower hκ0 hκ1 V hV hV0
        (angularBasis.repr (nativeHighProjection (angularEmbedding b))) t) := rfl

theorem nativeHalfHighPotentialPoissonCLM_zero (b : AngularH1) :
    nativeHalfHighPotentialPoissonCLM hκ0 hκ1 V hV hV0 b 0 =
      angularEmbedding (nativeHighEnergyProjectionCLM b) := by
  rw [nativeHalfHighPotentialPoissonCLM_apply, spectralHalfPotentialPoissonCLM_zero,
    LinearIsometryEquiv.symm_apply_apply, nativeHighEnergyProjectionCLM_embedding]

theorem nativeHalfHighPotentialPoissonCLM_norm_le (b : AngularH1) :
    ‖nativeHalfHighPotentialPoissonCLM hκ0 hκ1 V hV hV0 b‖ ≤ ‖b‖ / (1 - κ) := by
  have hEmb : ‖angularEmbedding b‖ ≤ ‖b‖ :=
    PoincareMT.LeviCivitaData.Dirichlet.norm_toDomainL2_le b
  have hbound := spectralHalfPotentialPoissonCLM_norm_le nativeAngularRate
    (by norm_num) nativeAngularRate_lower hκ0 hκ1 V hV hV0
    (angularBasis.repr (nativeHighProjection (angularEmbedding b)))
  apply (BoundedContinuousFunction.norm_le (div_nonneg (norm_nonneg b) (sub_pos.mpr hκ1).le)).mpr
  intro t
  rw [nativeHalfHighPotentialPoissonCLM_apply, LinearIsometryEquiv.norm_map]
  apply ((BoundedContinuousFunction.norm_coe_le_norm _ t).trans hbound).trans
  rw [LinearIsometryEquiv.norm_map]
  exact div_le_div_of_nonneg_right
    ((nativeAngularProjection_apply_norm_le _ (angularEmbedding b)).trans hEmb) (sub_pos.mpr hκ1).le

#print axioms nativeHighEnergyProjectionCLM_embedding
#print axioms nativeHighEnergyEntranceCLM_embedding_repr
#print axioms nativeHighEnergyEntranceCLM_norm_le
#print axioms nativeHalfHighPotentialPoissonCLM_zero
#print axioms nativeHalfHighPotentialPoissonCLM_norm_le

end Yamabe3.Analysis.Delaunay
