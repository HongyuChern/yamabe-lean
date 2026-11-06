import Yamabe3.Analysis.SpectralRootConvolution
import Yamabe3.Analysis.SpectralIntegralLinearity
import Yamabe3.Analysis.Sphere.NativeSphereEnergyBasis
import Yamabe3.Analysis.NativeAngularInverse

/-!
# The same canonical spectral inverse takes values in the actual native H1

The aggregate square-root convolution is a genuine L2 vector. A bounded
ratio sqrt(1+lambda)/k transports it through the proved native H1 Hilbert
basis. Its actual native L2 embedding is then exactly the same canonical
R_V value, coefficient by coefficient. This gives a real H1 entrance value
for the forced half-end construction, rather than assuming that an
arbitrary angular L2 boundary function has an H1 lifting.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000

open Set Filter MeasureTheory PoincareMT
open scoped Topology lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

open SphereSpectrum

private theorem native_energy_rate_ratio_bound (i : AngularIndex) :
    |angularEnergyWeight i / nativeAngularRate i| ≤ 2 := by
  have hk : 0 < nativeAngularRate i := by have := nativeAngularRate_lower i; linarith
  have hw : 0 < angularEnergyWeight i := angularEnergyWeight_pos i
  have hwsq := angularEnergyWeight_sq i
  have hksq := nativeAngularRate_sq i
  have hl : angularEigenvalue i ≤ max 6 (angularEigenvalue i) := le_max_right _ _
  have hg := nativeAngularRate_lower i
  have hupper : angularEnergyWeight i ≤ 2 * nativeAngularRate i := by nlinarith
  rw [abs_of_pos (div_pos hw hk)]
  exact (div_le_iff₀ hk).mpr hupper

/-- The real native H1 synthesis of a spectral root vector.  This is a
bounded operator on the root vector, not on unrestricted L2 values. -/
def nativeSpectralRootEnergyCLM : SpectralSpace AngularIndex →L[ℝ] AngularH1 :=
  angularEnergyBasis.repr.symm.toLinearIsometry.toContinuousLinearMap.comp
    (spectralDiagonal (fun i => angularEnergyWeight i / nativeAngularRate i)
      (by norm_num : (0 : ℝ) ≤ 2) native_energy_rate_ratio_bound)

theorem nativeSpectralRootEnergyCLM_norm_le (r : SpectralSpace AngularIndex) :
    ‖nativeSpectralRootEnergyCLM r‖ ≤ 2 * ‖r‖ := by
  change ‖angularEnergyBasis.repr.symm
    (spectralDiagonal (fun i => angularEnergyWeight i / nativeAngularRate i)
      (by norm_num : (0 : ℝ) ≤ 2) native_energy_rate_ratio_bound r)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (spectralDiagonal_norm_le _ (by norm_num : (0 : ℝ) ≤ 2)
        native_energy_rate_ratio_bound) (norm_nonneg r))

theorem nativeSpectralRootEnergyCLM_embedding_coefficient
    (r : SpectralSpace AngularIndex) (i : AngularIndex) :
    inner ℝ (angularBasis i) (angularEmbedding (nativeSpectralRootEnergyCLM r)) =
      r i / nativeAngularRate i := by
  have h := (angularEnergyBasis_synthesis_spec
    (spectralDiagonal (fun j => angularEnergyWeight j / nativeAngularRate j)
      (by norm_num : (0 : ℝ) ≤ 2) native_energy_rate_ratio_bound r)).1 i
  change inner ℝ (angularBasis i) (angularEmbedding (nativeSpectralRootEnergyCLM r)) = _ at h
  rw [spectralDiagonal_apply] at h
  rw [h]
  have hw : angularEnergyWeight i ≠ 0 := (angularEnergyWeight_pos i).ne'
  have hk : nativeAngularRate i ≠ 0 := by have := nativeAngularRate_lower i; linarith
  field_simp [hw, hk]

/-- Whenever the input is an actual root of a given spectral vector, the
result is its genuine native H1 representative, with the same L2 value. -/
theorem nativeSpectralRootEnergyCLM_embedding
    (w r : SpectralSpace AngularIndex) (hr : ∀ i, r i = nativeAngularRate i * w i) :
    angularEmbedding (nativeSpectralRootEnergyCLM r) = angularBasis.repr.symm w := by
  apply angularBasis.repr.injective
  ext i
  rw [HilbertBasis.repr_apply_apply, nativeSpectralRootEnergyCLM_embedding_coefficient,
    hr i, LinearIsometryEquiv.apply_symm_apply]
  have hk : nativeAngularRate i ≠ 0 := by have := nativeAngularRate_lower i; linarith
  exact mul_div_cancel_left₀ (w i) hk

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)

/-- The actual energy representative of the original canonical fixed
point. No new weak solution or independent representative is selected. -/
def nativeIntegralPotentialEnergy
    (F : ℝ →ᵇ SpectralSpace AngularIndex) (t : ℝ) : AngularH1 :=
  nativeSpectralRootEnergyCLM
    (spectralIntegralPotentialRoot nativeAngularRate (by norm_num) nativeAngularRate_lower
      (by norm_num : |(-2 : ℝ)| < (5 / 2 : ℝ)) hκ0 hκ1 V hV F t)

theorem nativeIntegralPotentialEnergy_embedding
    (F : ℝ →ᵇ SpectralSpace AngularIndex) (t : ℝ) :
    angularEmbedding (nativeIntegralPotentialEnergy hκ0 hκ1 V hV F t) =
      angularBasis.repr.symm
        (spectralIntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
          (by norm_num : |(-2 : ℝ)| < (5 / 2 : ℝ)) hκ0 hκ1 V hV F t) := by
  apply nativeSpectralRootEnergyCLM_embedding
  exact fun i => spectralIntegralPotentialRoot_coordinate nativeAngularRate (by norm_num)
    nativeAngularRate_lower (by norm_num : |(-2 : ℝ)| < (5 / 2 : ℝ)) hκ0 hκ1 V hV F t i

theorem nativeIntegralPotentialEnergy_norm_le
    (F : ℝ →ᵇ SpectralSpace AngularIndex) (t : ℝ) :
    ‖nativeIntegralPotentialEnergy hκ0 hκ1 V hV F t‖ ≤
      (20 / 9 : ℝ) * (1 + (4 / 9 : ℝ) * ‖V‖ / (1 - κ)) * ‖F‖ := by
  have hR := spectralIntegralPotentialRoot_norm_le nativeAngularRate (by norm_num)
    nativeAngularRate_lower (by norm_num : |(-2 : ℝ)| < (5 / 2 : ℝ))
    hκ0 hκ1 V hV F t
  calc
    _ ≤ 2 * ‖spectralIntegralPotentialRoot nativeAngularRate (by norm_num)
        nativeAngularRate_lower (by norm_num : |(-2 : ℝ)| < (5 / 2 : ℝ))
        hκ0 hκ1 V hV F t‖ := nativeSpectralRootEnergyCLM_norm_le _
    _ ≤ 2 * ((5 / 2 / ((5 / 2 : ℝ) ^ 2 - (-2) ^ 2)) *
        (1 + ‖V‖ / (((5 / 2 : ℝ) ^ 2 - (-2) ^ 2) * (1 - κ))) * ‖F‖) :=
      mul_le_mul_of_nonneg_left hR (by norm_num)
    _ = _ := by
      norm_num
      field_simp [(sub_pos.mpr hκ1).ne'] <;> ring

theorem nativeIntegralPotentialEnergy_continuous
    (F : ℝ →ᵇ SpectralSpace AngularIndex) :
    Continuous (nativeIntegralPotentialEnergy hκ0 hκ1 V hV F) := by
  apply nativeSpectralRootEnergyCLM.continuous.comp
  exact spectralRootConvolution_continuous nativeAngularRate (by norm_num)
    nativeAngularRate_lower (by norm_num : |(-2 : ℝ)| < (5 / 2 : ℝ)) _

/-- Evaluation of the same inverse in the actual H1 space is a bounded
linear map. Linearity follows through the injective actual L2 embedding. -/
def nativeIntegralPotentialEnergyAtCLM (t : ℝ) :
    (ℝ →ᵇ SpectralSpace AngularIndex) →L[ℝ] AngularH1 :=
  ({ toFun := fun F => nativeIntegralPotentialEnergy hκ0 hκ1 V hV F t
     map_add' := by
       intro F G
       apply angularEmbedding_injective
       rw [map_add, nativeIntegralPotentialEnergy_embedding,
         nativeIntegralPotentialEnergy_embedding, nativeIntegralPotentialEnergy_embedding]
       change angularBasis.repr.symm
           (spectralIntegralPotentialInverseCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
             (by norm_num : |(-2 : ℝ)| < (5 / 2 : ℝ)) hκ0 hκ1 V hV (F + G) t) = _
       rw [map_add, BoundedContinuousFunction.add_apply, map_add]
       rfl
     map_smul' := by
       intro c F
       apply angularEmbedding_injective
       rw [map_smul, nativeIntegralPotentialEnergy_embedding, nativeIntegralPotentialEnergy_embedding]
       change angularBasis.repr.symm
           (spectralIntegralPotentialInverseCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
             (by norm_num : |(-2 : ℝ)| < (5 / 2 : ℝ)) hκ0 hκ1 V hV (c • F) t) = _
       rw [map_smul, BoundedContinuousFunction.smul_apply, map_smul]
       rfl } :
      (ℝ →ᵇ SpectralSpace AngularIndex) →ₗ[ℝ] AngularH1).mkContinuous
    ((20 / 9 : ℝ) * (1 + (4 / 9 : ℝ) * ‖V‖ / (1 - κ)))
    (fun F => nativeIntegralPotentialEnergy_norm_le hκ0 hκ1 V hV F t)

theorem nativeIntegralPotentialEnergyAtCLM_apply
    (F : ℝ →ᵇ SpectralSpace AngularIndex) (t : ℝ) :
    nativeIntegralPotentialEnergyAtCLM hκ0 hκ1 V hV t F =
      nativeIntegralPotentialEnergy hκ0 hκ1 V hV F t := rfl

#print axioms nativeSpectralRootEnergyCLM_embedding
#print axioms nativeIntegralPotentialEnergy_embedding
#print axioms nativeIntegralPotentialEnergy_norm_le
#print axioms nativeIntegralPotentialEnergyAtCLM

end Yamabe3.Analysis.Delaunay
