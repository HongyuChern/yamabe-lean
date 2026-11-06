import Yamabe3.Analysis.NativeForcedHalfEndEnergyApproximation
import Mathlib.Order.Filter.AtTopBot.Prod

/-!
# Genuine two-index Cauchy energy for the original finite spectral fields

Every finite-pair square integral is first proved integrable.  The
two-error square estimate then bounds it by the two genuine one-index
errors, which converge along the full finite-set filter.  The resulting
limit is on `Finset AngularIndex × Finset AngularIndex` with its product
order `atTop`, without choosing a sequence or changing either curve.

The actual native L2 inclusion contracts differences of the same H1
finite projections.  Its proved embedding identity therefore controls
the original finite field differences by these same H1 differences.
No global Euclidean Sobolev conclusion is asserted in this file.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

section HilbertProjection

variable {H ι α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace α] {μ : Measure α}

/-- The actual pair difference is controlled by the two errors to the
same original vector. -/
theorem finiteHilbertProjection_pair_sub_norm_sq_le
    (b : HilbertBasis ι ℝ H) (s t : Finset ι) (x : H) :
    ‖finiteHilbertProjection b s x - finiteHilbertProjection b t x‖ ^ 2 ≤
      2 * ‖finiteHilbertProjection b s x - x‖ ^ 2 +
        2 * ‖finiteHilbertProjection b t x - x‖ ^ 2 := by
  have hn : ‖finiteHilbertProjection b s x - finiteHilbertProjection b t x‖ ≤
      ‖finiteHilbertProjection b s x - x‖ + ‖finiteHilbertProjection b t x - x‖ := by
    calc
      _ = ‖(finiteHilbertProjection b s x - x) -
          (finiteHilbertProjection b t x - x)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
  nlinarith only [hs, sq_nonneg
    (‖finiteHilbertProjection b s x - x‖ - ‖finiteHilbertProjection b t x - x‖)]

/-- Each real pair-error integral exists before any comparison or limit. -/
theorem finiteHilbertProjection_pair_error_integrable_of_memLp
    (b : HilbertBasis ι ℝ H) (s t : Finset ι) {U : α → H} (hU : MemLp U 2 μ) :
    Integrable (fun x => ‖finiteHilbertProjection b s (U x) -
      finiteHilbertProjection b t (U x)‖ ^ 2) μ := by
  have hs := finiteHilbertProjection_error_integrable_of_memLp b s hU
  have ht := finiteHilbertProjection_error_integrable_of_memLp b t hU
  have hmajor := (hs.const_mul 2).add (ht.const_mul 2)
  apply hmajor.mono'
    ((((continuous_finiteHilbertProjection b s).comp_aestronglyMeasurable hU.1).sub
      ((continuous_finiteHilbertProjection b t).comp_aestronglyMeasurable hU.1)).norm.pow 2)
  exact Eventually.of_forall fun x => by
    change ‖‖finiteHilbertProjection b s (U x) - finiteHilbertProjection b t (U x)‖ ^ 2‖ ≤
      2 * ‖finiteHilbertProjection b s (U x) - U x‖ ^ 2 +
        2 * ‖finiteHilbertProjection b t (U x) - U x‖ ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact finiteHilbertProjection_pair_sub_norm_sq_le b s t (U x)

theorem finiteHilbertProjection_pair_integral_error_le
    (b : HilbertBasis ι ℝ H) (s t : Finset ι) {U : α → H} (hU : MemLp U 2 μ) :
    (∫ x, ‖finiteHilbertProjection b s (U x) - finiteHilbertProjection b t (U x)‖ ^ 2 ∂μ) ≤
      2 * (∫ x, ‖finiteHilbertProjection b s (U x) - U x‖ ^ 2 ∂μ) +
        2 * (∫ x, ‖finiteHilbertProjection b t (U x) - U x‖ ^ 2 ∂μ) := by
  have hs := finiteHilbertProjection_error_integrable_of_memLp b s hU
  have ht := finiteHilbertProjection_error_integrable_of_memLp b t hU
  calc
    _ ≤ ∫ x, 2 * ‖finiteHilbertProjection b s (U x) - U x‖ ^ 2 +
        2 * ‖finiteHilbertProjection b t (U x) - U x‖ ^ 2 ∂μ := by
      apply integral_mono_ae
        (finiteHilbertProjection_pair_error_integrable_of_memLp b s t hU)
        ((hs.const_mul 2).add (ht.const_mul 2))
      exact Eventually.of_forall fun x => finiteHilbertProjection_pair_sub_norm_sq_le b s t (U x)
    _ = _ := by
      rw [integral_add (hs.const_mul 2) (ht.const_mul 2), integral_const_mul, integral_const_mul]

/-- A genuine full two-index finite-set net.  Both indices are free to
increase independently and the underlying function remains the same. -/
theorem finiteHilbertProjection_pair_integral_error_tendsto_finset
    [Countable ι] (b : HilbertBasis ι ℝ H) {U : α → H} (hU : MemLp U 2 μ) :
    Tendsto (fun p : Finset ι × Finset ι =>
      ∫ x, ‖finiteHilbertProjection b p.1 (U x) -
        finiteHilbertProjection b p.2 (U x)‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hlim : Tendsto (fun s : Finset ι =>
      ∫ x, ‖finiteHilbertProjection b s (U x) - U x‖ ^ 2 ∂μ) atTop (𝓝 0) :=
    finiteHilbertProjection_integral_error_tendsto_of_memLp b tendsto_id hU
  have hfst : Tendsto (Prod.fst : Finset ι × Finset ι → Finset ι) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : Finset ι × Finset ι → Finset ι) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hbound := ((hlim.comp hfst).const_mul (2 : ℝ)).add
    ((hlim.comp hsnd).const_mul (2 : ℝ))
  simp only [mul_zero, zero_add] at hbound
  exact squeeze_zero (fun p => integral_nonneg (fun x => sq_nonneg _))
    (fun p => finiteHilbertProjection_pair_integral_error_le b p.1 p.2 hU) hbound

end HilbertProjection

open SphereSpectrum Poincare.Geometry.Riemannian.SpaceForm

/-- The same finite H1 difference controls its actual L2 image. -/
theorem native_finiteEnergyProjection_sub_norm_le
    (s t : Finset AngularIndex) (u : AngularH1) :
    ‖finiteHilbertProjection angularBasis s (angularEmbedding u) -
      finiteHilbertProjection angularBasis t (angularEmbedding u)‖ ≤
        ‖finiteHilbertProjection angularEnergyBasis s u -
          finiteHilbertProjection angularEnergyBasis t u‖ := by
  have h := PoincareMT.LeviCivitaData.Dirichlet.norm_toDomainL2_le
    (finiteHilbertProjection angularEnergyBasis s u -
      finiteHilbertProjection angularEnergyBasis t u)
  change ‖angularEmbedding (finiteHilbertProjection angularEnergyBasis s u -
    finiteHilbertProjection angularEnergyBasis t u)‖ ≤ _ at h
  rw [map_sub, native_finiteEnergyProjection_embedding, native_finiteEnergyProjection_embedding] at h
  exact h

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

theorem nativeHalfHighDirichletPhysical_finite_sub_norm_le
    (F : ℝ≥0 →ᵇ AngularL2) (s t : Finset AngularIndex) (r : ℝ) :
    ‖finiteHilbertProjection angularBasis s
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F r) -
      finiteHilbertProjection angularBasis t
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F r)‖ ≤
    ‖finiteHilbertProjection angularEnergyBasis s
        (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r) -
      finiteHilbertProjection angularEnergyBasis t
        (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r)‖ := by
  simpa only [nativeHalfHighDirichletPhysicalEnergy_embedding] using
    native_finiteEnergyProjection_sub_norm_le s t
      (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r)

theorem nativeHalfHighDirichletPhysical_finite_sub_norm_sq_le
    (F : ℝ≥0 →ᵇ AngularL2) (s t : Finset AngularIndex) (r : ℝ) :
    ‖finiteHilbertProjection angularBasis s
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F r) -
      finiteHilbertProjection angularBasis t
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F r)‖ ^ 2 ≤
    ‖finiteHilbertProjection angularEnergyBasis s
        (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r) -
      finiteHilbertProjection angularEnergyBasis t
        (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r)‖ ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _)
    (nativeHalfHighDirichletPhysical_finite_sub_norm_le hκ0 hκ1 V hV hV0 F s t r) 2

/-- Both actual finite-pair terms are integrable on the entire half-line. -/
theorem nativeHalfHighDirichletPhysical_pair_energy_integrable
    (F : ℝ≥0 →ᵇ AngularL2) (s t : Finset AngularIndex) :
    IntegrableOn (fun r : ℝ =>
      ‖finiteHilbertProjection angularEnergyBasis s
          (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r) -
        finiteHilbertProjection angularEnergyBasis t
          (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r)‖ ^ 2 +
      ‖finiteHilbertProjection angularBasis s
          (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r) -
        finiteHilbertProjection angularBasis t
          (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r)‖ ^ 2) (Ici 0) :=
  (finiteHilbertProjection_pair_error_integrable_of_memLp angularEnergyBasis s t
    (nativeHalfHighDirichletPhysicalEnergy_memLp hκ0 hκ1 V hV hV0 F)).add
    (finiteHilbertProjection_pair_error_integrable_of_memLp angularBasis s t
      (nativeHalfHighDirichletPhysicalDerivative_memLp hκ0 hκ1 V hV hV0 F))

/-- The original actual finite spectral fields are Cauchy in the full
half-line energy, along the genuine independent two-index finite-set net. -/
theorem nativeHalfHighDirichletPhysical_pair_energy_tendsto_finset
    (F : ℝ≥0 →ᵇ AngularL2) :
    Tendsto (fun p : Finset AngularIndex × Finset AngularIndex => ∫ r in Ici (0 : ℝ),
      ‖finiteHilbertProjection angularEnergyBasis p.1
          (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r) -
        finiteHilbertProjection angularEnergyBasis p.2
          (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r)‖ ^ 2 +
      ‖finiteHilbertProjection angularBasis p.1
          (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r) -
        finiteHilbertProjection angularBasis p.2
          (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r)‖ ^ 2)
      atTop (𝓝 0) := by
  letI : Countable AngularIndex :=
    Poincare.Analysis.Dirichlet.CompactSpectral.countable_basisIndex
      (PoincareMT.LeviCivitaData.Dirichlet.domainL2Resolvent
        (roundSphereMetric 2).leviCivitaData univ)
      (PoincareMT.LeviCivitaData.Dirichlet.isCompactOperator_domainL2Resolvent
        (roundSphereMetric 2).leviCivitaData univ (by decide) isOpen_univ
        (by simpa using (isCompact_univ : IsCompact (univ : Set (UnitSphere 2)))))
      PoincareMT.LeviCivitaData.Dirichlet.domainL2Resolvent_isSelfAdjoint
  have hU := nativeHalfHighDirichletPhysicalEnergy_memLp hκ0 hκ1 V hV hV0 F
  have hD := nativeHalfHighDirichletPhysicalDerivative_memLp hκ0 hκ1 V hV hV0 F
  have hlimU := finiteHilbertProjection_pair_integral_error_tendsto_finset angularEnergyBasis hU
  have hlimD := finiteHilbertProjection_pair_integral_error_tendsto_finset angularBasis hD
  have heq (p : Finset AngularIndex × Finset AngularIndex) :
      (∫ r in Ici (0 : ℝ),
        ‖finiteHilbertProjection angularEnergyBasis p.1
            (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r) -
          finiteHilbertProjection angularEnergyBasis p.2
            (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r)‖ ^ 2 +
        ‖finiteHilbertProjection angularBasis p.1
            (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r) -
          finiteHilbertProjection angularBasis p.2
            (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r)‖ ^ 2) =
      (∫ r in Ici (0 : ℝ),
        ‖finiteHilbertProjection angularEnergyBasis p.1
            (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r) -
          finiteHilbertProjection angularEnergyBasis p.2
            (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r)‖ ^ 2) +
      (∫ r in Ici (0 : ℝ),
        ‖finiteHilbertProjection angularBasis p.1
            (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r) -
          finiteHilbertProjection angularBasis p.2
            (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r)‖ ^ 2) :=
    integral_add
      (finiteHilbertProjection_pair_error_integrable_of_memLp angularEnergyBasis p.1 p.2 hU)
      (finiteHilbertProjection_pair_error_integrable_of_memLp angularBasis p.1 p.2 hD)
  simp_rw [heq]
  simpa only [zero_add] using hlimU.add hlimD

#print axioms finiteHilbertProjection_pair_error_integrable_of_memLp
#print axioms finiteHilbertProjection_pair_integral_error_tendsto_finset
#print axioms nativeHalfHighDirichletPhysical_finite_sub_norm_le
#print axioms nativeHalfHighDirichletPhysical_finite_sub_norm_sq_le
#print axioms nativeHalfHighDirichletPhysical_pair_energy_integrable
#print axioms nativeHalfHighDirichletPhysical_pair_energy_tendsto_finset

end Yamabe3.Analysis.Delaunay
