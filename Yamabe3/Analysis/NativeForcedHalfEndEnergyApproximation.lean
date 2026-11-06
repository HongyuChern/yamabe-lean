import Yamabe3.Analysis.NativeForcedHalfEndCylinderEnergy
import Yamabe3.Analysis.HilbertFiniteProjectionFilter
import PoincareLib.Analysis.Parabolic.Dirichlet.SpectralCompactness

/-!
# The actual full spectral net converges in half-line energy

Finite projection in the genuine angular H1 Hilbert basis has exactly
the original native L2 finite projection as its actual embedding.  The
corresponding finite original L2 curves have the projected actual strong
time derivatives, including their right derivatives at the entrance.

The already produced full-half-line L2 bounds supply a true integrable
majorant.  Filter dominated convergence therefore proves convergence of
the entire finite-set net in the sum of angular H1 and time-derivative
L2 square integrals.  No uniform-in-time convergence of the source's
spectral truncations is assumed or inferred.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

section HilbertProjection

variable {H ι α J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace α] {μ : Measure α}

/-- The actual finite projection, now as its finite continuous linear sum. -/
def finiteHilbertProjectionCLM (b : HilbertBasis ι ℝ H) (s : Finset ι) : H →L[ℝ] H :=
  ∑ i ∈ s, (innerSL ℝ (b i)).smulRight (b i)

theorem finiteHilbertProjectionCLM_apply (b : HilbertBasis ι ℝ H) (s : Finset ι) (x : H) :
    finiteHilbertProjectionCLM b s x = finiteHilbertProjection b s x := by
  simp only [finiteHilbertProjectionCLM, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, finiteHilbertProjection] <;> rfl

/-- Integrability of each actual projection error follows from the
given square-integrable Hilbert curve, for an arbitrary measure. -/
theorem finiteHilbertProjection_error_integrable_of_memLp
    (b : HilbertBasis ι ℝ H) (s : Finset ι) {U : α → H} (hU : MemLp U 2 μ) :
    Integrable (fun x => ‖finiteHilbertProjection b s (U x) - U x‖ ^ 2) μ := by
  have hbound : Integrable (fun x => 4 * ‖U x‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm hU.1).mp hU).const_mul 4
  apply hbound.mono'
    ((((continuous_finiteHilbertProjection b s).comp_aestronglyMeasurable hU.1).sub hU.1).norm.pow 2)
  exact Eventually.of_forall fun x => by
    change ‖‖finiteHilbertProjection b s (U x) - U x‖ ^ 2‖ ≤ 4 * ‖U x‖ ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact finiteHilbertProjection_sub_norm_sq_le b s (U x)

/-- Genuine filter convergence in L2 for any actual square-integrable
Hilbert-valued function.  The measure need not have finite mass. -/
theorem finiteHilbertProjection_integral_error_tendsto_of_memLp
    (b : HilbertBasis ι ℝ H) {l : Filter J} [l.IsCountablyGenerated]
    {s : J → Finset ι} (hs : Tendsto s l atTop) {U : α → H} (hU : MemLp U 2 μ) :
    Tendsto (fun j => ∫ x, ‖finiteHilbertProjection b (s j) (U x) - U x‖ ^ 2 ∂μ)
      l (𝓝 0) := by
  have hbound : Integrable (fun x => 4 * ‖U x‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm hU.1).mp hU).const_mul 4
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := l) (fun x => 4 * ‖U x‖ ^ 2)
    (F := fun j x => ‖finiteHilbertProjection b (s j) (U x) - U x‖ ^ 2)
    (f := fun _ => (0 : ℝ))
    (Eventually.of_forall fun j =>
      ((((continuous_finiteHilbertProjection b (s j)).comp_aestronglyMeasurable hU.1).sub
        hU.1).norm.pow 2))
    (Eventually.of_forall fun j => Eventually.of_forall fun x => by
      change ‖‖finiteHilbertProjection b (s j) (U x) - U x‖ ^ 2‖ ≤ 4 * ‖U x‖ ^ 2
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact finiteHilbertProjection_sub_norm_sq_le b (s j) (U x))
    hbound
    (Eventually.of_forall fun x => by
      simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
        ((finiteHilbertProjection_tendsto_filter b hs (U x)).sub
          (tendsto_const_nhds (x := U x))).norm.pow 2)
  simpa only [integral_zero] using h

end HilbertProjection

open SphereSpectrum Poincare.Geometry.Riemannian.SpaceForm

/-- The energy projection has the original L2 finite projection as its
faithful actual embedding, with the same finite set and coefficients. -/
theorem native_finiteEnergyProjection_embedding (s : Finset AngularIndex) (u : AngularH1) :
    angularEmbedding (finiteHilbertProjection angularEnergyBasis s u) =
      finiteHilbertProjection angularBasis s (angularEmbedding u) := by
  simp only [finiteHilbertProjection, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  have hcoeff : inner ℝ (angularEnergyBasis i) u =
      angularEnergyWeight i * inner ℝ (angularBasis i) (angularEmbedding u) := by
    rw [angularEnergyBasis_apply, angularNormalizedEnergyMode_inner]
  have hmode : angularEmbedding (angularEnergyBasis i) =
      (angularEnergyWeight i)⁻¹ • angularBasis i := by
    rw [angularEnergyBasis_apply, angularNormalizedEnergyMode, map_smul, angularEmbedding_energyMode]
  rw [hcoeff, hmode, smul_smul]
  congr 1
  field_simp [(angularEnergyWeight_pos i).ne'] <;> ring

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

theorem nativeHalfHighDirichletPhysical_finiteEnergy_embedding
    (F : ℝ≥0 →ᵇ AngularL2) (s : Finset AngularIndex) (t : ℝ) :
    angularEmbedding (finiteHilbertProjection angularEnergyBasis s
      (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F t)) =
      finiteHilbertProjection angularBasis s
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t) := by
  rw [native_finiteEnergyProjection_embedding, nativeHalfHighDirichletPhysicalEnergy_embedding]

/-- Differentiation of the actual finite original curve produces
precisely the finite projection of the already constructed derivative. -/
theorem nativeHalfHighDirichletPhysical_finite_hasDerivWithinAt
    (F : ℝ≥0 →ᵇ AngularL2) (s : Finset AngularIndex) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt
      (fun r => finiteHilbertProjection angularBasis s
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F r))
      (finiteHilbertProjection angularBasis s
        (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t)) (Ici 0) t := by
  simpa only [Function.comp_def, finiteHilbertProjectionCLM_apply] using
    (finiteHilbertProjectionCLM angularBasis s).hasFDerivAt.comp_hasDerivWithinAt t
      (nativeHalfHighDirichletPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 F t ht)

/-- A cofinal family converges in the genuine full-half-line energy
norm of the actual H1 representative and actual strong derivative. -/
theorem nativeHalfHighDirichletPhysical_energy_error_tendsto_filter
    (F : ℝ≥0 →ᵇ AngularL2) {J : Type*} {l : Filter J} [l.IsCountablyGenerated]
    {s : J → Finset AngularIndex} (hs : Tendsto s l atTop) :
    Tendsto (fun j => ∫ t in Ici (0 : ℝ),
      ‖finiteHilbertProjection angularEnergyBasis (s j)
          (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F t) -
        nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F t‖ ^ 2 +
      ‖finiteHilbertProjection angularBasis (s j)
          (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t) -
        nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t‖ ^ 2)
      l (𝓝 0) := by
  have hU := nativeHalfHighDirichletPhysicalEnergy_memLp hκ0 hκ1 V hV hV0 F
  have hD := nativeHalfHighDirichletPhysicalDerivative_memLp hκ0 hκ1 V hV hV0 F
  have hlimU := finiteHilbertProjection_integral_error_tendsto_of_memLp angularEnergyBasis hs hU
  have hlimD := finiteHilbertProjection_integral_error_tendsto_of_memLp angularBasis hs hD
  have heq (j : J) :
      (∫ t in Ici (0 : ℝ),
        ‖finiteHilbertProjection angularEnergyBasis (s j)
            (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F t) -
          nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F t‖ ^ 2 +
        ‖finiteHilbertProjection angularBasis (s j)
            (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t) -
          nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t‖ ^ 2) =
      (∫ t in Ici (0 : ℝ),
        ‖finiteHilbertProjection angularEnergyBasis (s j)
            (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F t) -
          nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F t‖ ^ 2) +
      (∫ t in Ici (0 : ℝ),
        ‖finiteHilbertProjection angularBasis (s j)
            (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t) -
          nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t‖ ^ 2) :=
    integral_add
      (finiteHilbertProjection_error_integrable_of_memLp angularEnergyBasis (s j) hU)
      (finiteHilbertProjection_error_integrable_of_memLp angularBasis (s j) hD)
  simp_rw [heq]
  simpa only [zero_add] using hlimU.add hlimD

/-- The entire finite-set net, without selecting an exhaustion sequence. -/
theorem nativeHalfHighDirichletPhysical_energy_error_tendsto_finset
    (F : ℝ≥0 →ᵇ AngularL2) :
    Tendsto (fun s : Finset AngularIndex => ∫ t in Ici (0 : ℝ),
      ‖finiteHilbertProjection angularEnergyBasis s
          (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F t) -
        nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F t‖ ^ 2 +
      ‖finiteHilbertProjection angularBasis s
          (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t) -
        nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t‖ ^ 2)
      atTop (𝓝 0) := by
  letI : Countable AngularIndex :=
    Poincare.Analysis.Dirichlet.CompactSpectral.countable_basisIndex
      (PoincareMT.LeviCivitaData.Dirichlet.domainL2Resolvent
        (roundSphereMetric 2).leviCivitaData univ)
      (PoincareMT.LeviCivitaData.Dirichlet.isCompactOperator_domainL2Resolvent
        (roundSphereMetric 2).leviCivitaData univ (by decide) isOpen_univ
        (by simpa using (isCompact_univ : IsCompact (univ : Set (UnitSphere 2)))))
      PoincareMT.LeviCivitaData.Dirichlet.domainL2Resolvent_isSelfAdjoint
  exact nativeHalfHighDirichletPhysical_energy_error_tendsto_filter hκ0 hκ1 V hV hV0 F tendsto_id

#print axioms finiteHilbertProjection_integral_error_tendsto_of_memLp
#print axioms native_finiteEnergyProjection_embedding
#print axioms nativeHalfHighDirichletPhysical_finiteEnergy_embedding
#print axioms nativeHalfHighDirichletPhysical_finite_hasDerivWithinAt
#print axioms nativeHalfHighDirichletPhysical_energy_error_tendsto_filter
#print axioms nativeHalfHighDirichletPhysical_energy_error_tendsto_finset

end Yamabe3.Analysis.Delaunay
