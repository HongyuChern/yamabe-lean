import Yamabe3.Analysis.NativeForcedHalfEndEnergyCauchy

/-!
# The actual finite spectral difference and its modal energy

The coefficients are those of the difference of the two original finite
projections of the same constructed forced field.  They equal the literal
two indicator coefficients and vanish outside the union of the original
finite sets.  The finite sum reconstructs that same projection difference.

Positive-time C2 regularity comes from the original coordinate producer.
Its actual first derivative is the corresponding coefficient of the
same produced strong derivative.  The genuine energy Bessel inequality
and the actual L2 Bessel inequality then control the finite radial and
angular modal energy.  No geometric gradient identity or extra estimate
is an input to this pure spectral bridge.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction

attribute [local instance] Classical.propDecidable

namespace Yamabe3.Analysis.Delaunay

section HilbertDifference

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem finiteHilbertProjection_coefficient
    (b : HilbertBasis ι ℝ H) (s : Finset ι) (x : H) (i : ι) :
    inner ℝ (b i) (finiteHilbertProjection b s x) =
      if i ∈ s then inner ℝ (b i) x else 0 := by
  classical
  simp only [finiteHilbertProjection, inner_sum, real_inner_smul_right]
  have hb (j : ι) : inner ℝ (b i) (b j) = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp b.orthonormal i j
  simp_rw [hb]
  by_cases hi : i ∈ s <;> simp [hi]

/-- Literal coefficients of two finite projections of the same vector. -/
def finiteHilbertDifferenceCoefficient
    (b : HilbertBasis ι ℝ H) (s t : Finset ι) (x : H) (i : ι) : ℝ :=
  inner ℝ (b i) (finiteHilbertProjection b s x - finiteHilbertProjection b t x)

theorem finiteHilbertDifferenceCoefficient_eq_if
    (b : HilbertBasis ι ℝ H) (s t : Finset ι) (x : H) (i : ι) :
    finiteHilbertDifferenceCoefficient b s t x i =
      (if i ∈ s then inner ℝ (b i) x else 0) -
        (if i ∈ t then inner ℝ (b i) x else 0) := by
  rw [finiteHilbertDifferenceCoefficient, inner_sub_right,
    finiteHilbertProjection_coefficient, finiteHilbertProjection_coefficient]

theorem finiteHilbertDifferenceCoefficient_eq_zero_of_not_mem
    (b : HilbertBasis ι ℝ H) (s t : Finset ι) (x : H) (i : ι) (hi : i ∉ s ∪ t) :
    finiteHilbertDifferenceCoefficient b s t x i = 0 := by
  have hs : i ∉ s := fun h => hi (Finset.mem_union_left t h)
  have ht : i ∉ t := fun h => hi (Finset.mem_union_right s h)
  rw [finiteHilbertDifferenceCoefficient_eq_if, if_neg hs, if_neg ht, sub_self]

/-- The coefficients on the actual union reconstruct the original pair
of finite projections, without choosing any different spectral vector. -/
theorem finiteHilbertDifferenceCoefficient_sum
    (b : HilbertBasis ι ℝ H) (s t : Finset ι) (x : H) :
    (∑ i ∈ s ∪ t, finiteHilbertDifferenceCoefficient b s t x i • b i) =
      finiteHilbertProjection b s x - finiteHilbertProjection b t x := by
  calc
    _ = finiteHilbertProjection b (s ∪ t)
        (finiteHilbertProjection b s x - finiteHilbertProjection b t x) := rfl
    _ = _ := by
      apply b.repr.injective
      ext i
      simp only [HilbertBasis.repr_apply_apply]
      rw [finiteHilbertProjection_coefficient]
      by_cases hi : i ∈ s ∪ t
      · rw [if_pos hi]
      · rw [if_neg hi]
        exact (finiteHilbertDifferenceCoefficient_eq_zero_of_not_mem b s t x i hi).symm

end HilbertDifference

open SphereSpectrum

private theorem finiteDifference_angularEigenvalue_nonneg (i : AngularIndex) :
    0 ≤ angularEigenvalue i := by
  rcases angularEigenvalue_zero_two_or_ge_six i with h | h | h
  · rw [h]
  · rw [h]; norm_num
  · linarith only [h]

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The original finite-pair coefficient, supported on the original union. -/
def nativeHalfHighDirichletFiniteDifferenceCoefficient
    (F : ℝ≥0 →ᵇ AngularL2) (s t : Finset AngularIndex) (i : AngularIndex) (r : ℝ) : ℝ :=
  finiteHilbertDifferenceCoefficient angularBasis s t
    (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F r) i

theorem nativeHalfHighDirichletFiniteDifferenceCoefficient_apply
    (F : ℝ≥0 →ᵇ AngularL2) (s t : Finset AngularIndex) (i : AngularIndex) (r : ℝ) :
    nativeHalfHighDirichletFiniteDifferenceCoefficient hκ0 hκ1 V hV hV0 F s t i r =
      (if i ∈ s then inner ℝ (angularBasis i)
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F r) else 0) -
      (if i ∈ t then inner ℝ (angularBasis i)
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F r) else 0) :=
  finiteHilbertDifferenceCoefficient_eq_if angularBasis s t _ i

theorem nativeHalfHighDirichletFiniteDifferenceCoefficient_zero
    (F : ℝ≥0 →ᵇ AngularL2) (s t : Finset AngularIndex) (i : AngularIndex)
    (hi : i ∉ s ∪ t) (r : ℝ) :
    nativeHalfHighDirichletFiniteDifferenceCoefficient hκ0 hκ1 V hV hV0 F s t i r = 0 :=
  finiteHilbertDifferenceCoefficient_eq_zero_of_not_mem angularBasis s t _ i hi

theorem nativeHalfHighDirichletFiniteDifferenceCoefficient_sum
    (F : ℝ≥0 →ᵇ AngularL2) (s t : Finset AngularIndex) (r : ℝ) :
    (∑ i ∈ s ∪ t,
      nativeHalfHighDirichletFiniteDifferenceCoefficient hκ0 hκ1 V hV hV0 F s t i r •
        angularBasis i) =
      finiteHilbertProjection angularBasis s
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F r) -
      finiteHilbertProjection angularBasis t
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F r) :=
  finiteHilbertDifferenceCoefficient_sum angularBasis s t _

theorem nativeHalfHighDirichletFiniteDifferenceCoefficient_c2
    (F : ℝ≥0 →ᵇ AngularL2) (s t : Finset AngularIndex) (i : AngularIndex) :
    ContDiffOn ℝ 2
      (nativeHalfHighDirichletFiniteDifferenceCoefficient hκ0 hκ1 V hV hV0 F s t i) (Ioi 0) := by
  have hc := nativeHalfHighDirichletPhysical_coefficient_c2 hκ0 hκ1 V hV hV0 F i
  have hz : ContDiffOn ℝ 2 (fun _ : ℝ => (0 : ℝ)) (Ioi 0) := contDiffOn_const
  change ContDiffOn ℝ 2
    (fun r => finiteHilbertDifferenceCoefficient angularBasis s t
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F r) i) (Ioi 0)
  simp only [finiteHilbertDifferenceCoefficient_eq_if]
  by_cases hs : i ∈ s
  · by_cases ht : i ∈ t
    · simpa only [if_pos hs, if_pos ht] using hc.sub hc
    · simpa only [if_pos hs, if_neg ht] using hc.sub hz
  · by_cases ht : i ∈ t
    · simpa only [if_neg hs, if_pos ht] using hz.sub hc
    · simpa only [if_neg hs, if_neg ht] using hz.sub hz

/-- The derivative is produced from the actual strong derivative of
the same original field, rather than from a separate coefficient input. -/
theorem nativeHalfHighDirichletFiniteDifferenceCoefficient_hasDerivAt
    (F : ℝ≥0 →ᵇ AngularL2) (s t : Finset AngularIndex) (i : AngularIndex)
    (r : ℝ) (hr : 0 < r) :
    HasDerivAt (nativeHalfHighDirichletFiniteDifferenceCoefficient hκ0 hκ1 V hV hV0 F s t i)
      (finiteHilbertDifferenceCoefficient angularBasis s t
        (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r) i) r := by
  let A : AngularL2 →L[ℝ] AngularL2 :=
    finiteHilbertProjectionCLM angularBasis s - finiteHilbertProjectionCLM angularBasis t
  have hA := A.hasFDerivAt.comp_hasDerivAt r
    (nativeHalfHighDirichletPhysical_hasDerivAt hκ0 hκ1 V hV hV0 F r hr)
  have h := (innerSL ℝ (angularBasis i)).hasFDerivAt.comp_hasDerivAt r hA
  change HasDerivAt
    (fun q => finiteHilbertDifferenceCoefficient angularBasis s t
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F q) i)
    (finiteHilbertDifferenceCoefficient angularBasis s t
      (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r) i) r
  simpa only [finiteHilbertDifferenceCoefficient, Function.comp_def, A, ContinuousLinearMap.sub_apply,
    finiteHilbertProjectionCLM_apply, innerSL_apply_apply] using h

theorem nativeHalfHighDirichletFiniteDifferenceCoefficient_deriv_eq_coefficient
    (F : ℝ≥0 →ᵇ AngularL2) (s t : Finset AngularIndex) (i : AngularIndex)
    (r : ℝ) (hr : 0 < r) :
    deriv (nativeHalfHighDirichletFiniteDifferenceCoefficient hκ0 hκ1 V hV hV0 F s t i) r =
      finiteHilbertDifferenceCoefficient angularBasis s t
        (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r) i :=
  (nativeHalfHighDirichletFiniteDifferenceCoefficient_hasDerivAt hκ0 hκ1 V hV hV0 F s t i r hr).deriv

theorem nativeHalfHighDirichletFiniteDifferenceCoefficient_deriv
    (F : ℝ≥0 →ᵇ AngularL2) (s t : Finset AngularIndex) (i : AngularIndex)
    (r : ℝ) (hr : 0 < r) :
    deriv (nativeHalfHighDirichletFiniteDifferenceCoefficient hκ0 hκ1 V hV hV0 F s t i) r =
      (if i ∈ s then inner ℝ (angularBasis i)
        (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r) else 0) -
      (if i ∈ t then inner ℝ (angularBasis i)
        (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r) else 0) := by
  rw [nativeHalfHighDirichletFiniteDifferenceCoefficient_deriv_eq_coefficient
    hκ0 hκ1 V hV hV0 F s t i r hr, finiteHilbertDifferenceCoefficient_eq_if]

/-- The true native finite modal energy is controlled by the same pair
of H1 and actual time-derivative L2 differences, with no auxiliary rate. -/
theorem nativeHalfHighDirichletFiniteDifference_modal_energy_le
    (F : ℝ≥0 →ᵇ AngularL2) (s t : Finset AngularIndex) (r : ℝ) (hr : 0 < r) :
    (∑ i ∈ (s ∪ t),
      ((deriv (nativeHalfHighDirichletFiniteDifferenceCoefficient hκ0 hκ1 V hV hV0 F s t i) r +
        nativeHalfHighDirichletFiniteDifferenceCoefficient hκ0 hκ1 V hV hV0 F s t i r / 2) ^ 2 +
      angularEigenvalue i *
        (nativeHalfHighDirichletFiniteDifferenceCoefficient hκ0 hκ1 V hV hV0 F s t i r) ^ 2)) ≤
    2 * (‖finiteHilbertProjection angularEnergyBasis s
          (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r) -
        finiteHilbertProjection angularEnergyBasis t
          (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r)‖ ^ 2 +
      ‖finiteHilbertProjection angularBasis s
          (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r) -
        finiteHilbertProjection angularBasis t
          (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r)‖ ^ 2) := by
  let E := finiteHilbertProjection angularEnergyBasis s
      (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r) -
    finiteHilbertProjection angularEnergyBasis t
      (nativeHalfHighDirichletPhysicalEnergy hκ0 hκ1 V hV hV0 F r)
  let D := finiteHilbertProjection angularBasis s
      (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r) -
    finiteHilbertProjection angularBasis t
      (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F r)
  let q := nativeHalfHighDirichletFiniteDifferenceCoefficient hκ0 hκ1 V hV hV0 F s t
  have hEmb : angularEmbedding E =
      finiteHilbertProjection angularBasis s
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F r) -
      finiteHilbertProjection angularBasis t
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F r) := by
    dsimp only [E]
    rw [map_sub, nativeHalfHighDirichletPhysical_finiteEnergy_embedding,
      nativeHalfHighDirichletPhysical_finiteEnergy_embedding]
  have hq (i : AngularIndex) : q i r = inner ℝ (angularBasis i) (angularEmbedding E) := by
    rw [hEmb]
    rfl
  have hd (i : AngularIndex) : deriv (q i) r = inner ℝ (angularBasis i) D :=
    nativeHalfHighDirichletFiniteDifferenceCoefficient_deriv_eq_coefficient
      hκ0 hκ1 V hV hV0 F s t i r hr
  have hE : (∑ i ∈ s ∪ t, (1 + angularEigenvalue i) * (q i r) ^ 2) ≤ ‖E‖ ^ 2 := by
    simpa only [hq] using finite_angular_energy_bound E (s ∪ t)
  have hD : (∑ i ∈ s ∪ t, (deriv (q i) r) ^ 2) ≤ ‖D‖ ^ 2 := by
    simp_rw [hd]
    simpa only [Real.norm_eq_abs, sq_abs] using
      angularBasis.orthonormal.sum_inner_products_le (s := s ∪ t) D
  have hi (i : AngularIndex) :
      (deriv (q i) r + q i r / 2) ^ 2 + angularEigenvalue i * (q i r) ^ 2 ≤
        2 * ((1 + angularEigenvalue i) * (q i r) ^ 2 + (deriv (q i) r) ^ 2) := by
    have hEig := finiteDifference_angularEigenvalue_nonneg i
    nlinarith only [sq_nonneg (deriv (q i) r - q i r / 2),
      mul_nonneg hEig (sq_nonneg (q i r)), sq_nonneg (q i r)]
  change (∑ i ∈ (s ∪ t), ((deriv (q i) r + q i r / 2) ^ 2 +
    angularEigenvalue i * (q i r) ^ 2)) ≤ 2 * (‖E‖ ^ 2 + ‖D‖ ^ 2)
  calc
    _ ≤ (∑ i ∈ (s ∪ t),
        2 * ((1 + angularEigenvalue i) * (q i r) ^ 2 + (deriv (q i) r) ^ 2)) :=
      Finset.sum_le_sum (fun i _hi => hi i)
    _ = 2 * ((∑ i ∈ s ∪ t, (1 + angularEigenvalue i) * (q i r) ^ 2) +
        (∑ i ∈ s ∪ t, (deriv (q i) r) ^ 2)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hE hD) (by norm_num)

#print axioms finiteHilbertDifferenceCoefficient_sum
#print axioms nativeHalfHighDirichletFiniteDifferenceCoefficient_zero
#print axioms nativeHalfHighDirichletFiniteDifferenceCoefficient_sum
#print axioms nativeHalfHighDirichletFiniteDifferenceCoefficient_c2
#print axioms nativeHalfHighDirichletFiniteDifferenceCoefficient_hasDerivAt
#print axioms nativeHalfHighDirichletFiniteDifferenceCoefficient_deriv
#print axioms nativeHalfHighDirichletFiniteDifference_modal_energy_le

end Yamabe3.Analysis.Delaunay
