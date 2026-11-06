import Yamabe3.Analysis.Cylinder.NativeSphereRestriction
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.DivergenceEquation
import Yamabe3.Analysis.NativeEuclideanVolume

/-!
# Actual coordinate extension is bounded in native energy on compact support

The estimate is proved for the genuine zero-extended coordinate function.
The constant is constructed from the actual retained density and inverse
metric coefficients on a fixed compact subset of the chart. It is uniform
over all smooth tests supported there. No assumed extension operator,
norm comparison, or Sobolev realization is an input.

This is the necessary native metric estimate for the completed angular
collar construction. It does not solve any boundary equation.
Actual Lean compilation pending.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open PoincareMT.LeviCivitaData.Dirichlet

universe u
variable {M : Type u} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

def nativeCoordinateEnergyTest (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (φ : EnergyTest euclideanD univ) (hφs : tsupport (φ : E → ℝ) ⊆ e.source) :
    EnergyTest g.leviCivitaData univ :=
  EnergyTest.ofCoordinates e hei φ φ.smooth.contDiff φ.hasCompactSupport
    (fun x hx => ⟨hφs hx, mem_univ _⟩)

@[simp] theorem nativeCoordinateEnergyTest_apply (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (φ : EnergyTest euclideanD univ) (hφs : tsupport (φ : E → ℝ) ⊆ e.source)
    (y : M) :
    nativeCoordinateEnergyTest g e hei φ hφs y = coordinateExtension e φ y := rfl

private theorem euclidean_partial_abs_le_gradient_norm
    (φ : EnergyTest euclideanD univ) (x : E) (i : Fin 3) :
    |fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1)| ≤
      (norm : E → ℝ) (euclideanD.gradient φ x) := by
  have he : (inner ℝ : E → E → ℝ) (euclideanD.gradient φ x) (EuclideanSpace.single i 1) =
      fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1) := by
    simpa only [RiemannianMetric.euclideanMetric_inner, mvfderiv,
      mfderiv_eq_fderiv, NormedSpace.fromTangentSpace, ContinuousLinearMap.comp_apply]
      using! euclideanD.inner_gradient (φ : E → ℝ) x (EuclideanSpace.single i 1)
  rw [← he]
  simpa only [EuclideanSpace.norm_single, norm_one, mul_one] using
    abs_real_inner_le_norm (F := E) (euclideanD.gradient φ x) (EuclideanSpace.single i (1 : ℝ))

private theorem coordinate_quadratic_le_absSum
    (A : Fin 3 → Fin 3 → ℝ) (φ : EnergyTest euclideanD univ) (x : E) :
    (∑ i, ∑ j, A i j * fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single j 1) *
      fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1)) ≤
        (∑ i, ∑ j, |A i j|) *
          (RiemannianMetric.euclideanMetric 3).inner x
            (euclideanD.gradient φ x) (euclideanD.gradient φ x) := by
  rw [RiemannianMetric.euclideanMetric_inner, real_inner_self_eq_norm_sq]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  have hi := euclidean_partial_abs_le_gradient_norm φ x i
  have hj := euclidean_partial_abs_le_gradient_norm φ x j
  calc
    _ ≤ |A i j * fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single j 1) *
      fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1)| := le_abs_self _
    _ = |A i j| * (|fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single j 1)| *
      |fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1)|) := by
        rw [abs_mul, abs_mul, mul_assoc]
    _ ≤ |A i j| * ((norm : E → ℝ) (euclideanD.gradient φ x) * (norm : E → ℝ) (euclideanD.gradient φ x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hj hi (abs_nonneg _) (norm_nonneg _))
        (abs_nonneg _)
    _ = _ := by rw [pow_two]

/-- The uniform compact-chart bound is derived internally from the actual
smooth positive metric. Its constant precedes the arbitrary coordinate
test and its support proof. -/
theorem exists_nativeCoordinateEnergyTest_bound
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : EnergyTest euclideanD univ)
      (hφK : tsupport (φ : E → ℝ) ⊆ K),
      ‖nativeCoordinateEnergyTest g e hei φ (hφK.trans hKs)‖ ≤ C * ‖φ‖ := by
  have hD : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) K := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds (hKs hx)))
      (hD.mfderiv_injective (hKs hx))).1.continuousAt.continuousWithinAt
  let σ : E → ℝ := fun x => |g.pullbackVolumeDensity e x| +
    ∑ i, ∑ j, |divergenceCoefficients g e x i j|
  have hσ : ContinuousOn σ K := hρ.abs.add
    (continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      ((contDiffOn_divergenceCoefficients (g := g) e he hei i j).continuousOn.mono hKs).abs)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hσ
  let C := max B 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hρC (x : E) (hx : x ∈ K) : g.pullbackVolumeDensity e x ≤ C := by
    have hsum : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, |divergenceCoefficients g e x i j| :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    have hb : σ x ≤ C := (le_abs_self _).trans ((hB x hx).trans (le_max_left _ _))
    exact (le_abs_self _).trans ((le_add_of_nonneg_right hsum).trans hb)
  have hAC (x : E) (hx : x ∈ K) :
      (∑ i : Fin 3, ∑ j : Fin 3, |divergenceCoefficients g e x i j|) ≤ C := by
    have hb : σ x ≤ C := (le_abs_self _).trans ((hB x hx).trans (le_max_left _ _))
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans hb
  refine ⟨Real.sqrt C, Real.sqrt_pos.2 hC, ?_⟩
  intro φ hφK
  let U := nativeCoordinateEnergyTest g e hei φ (hφK.trans hKs)
  let G : E → ℝ := fun x => (RiemannianMetric.euclideanMetric 3).inner x
    (euclideanD.gradient φ x) (euclideanD.gradient φ x)
  have hGcont : Continuous G := euclideanD.continuous_inner_gradient φ.smooth φ.smooth
  have hGnonneg (x : E) : 0 ≤ G x := by
    dsimp only [G]
    rw [RiemannianMetric.euclideanMetric_inner]
    exact real_inner_self_nonneg
  have hGi : Integrable G volume := by
    simpa only [native_euclideanMetric_volumeMeasure] using φ.integrable_gradient φ
  have hUimage : tsupport (U : M → ℝ) ⊆ e '' K :=
    (tsupport_coordinateExtension_subset_image e φ.hasCompactSupport (hφK.trans hKs)).trans (image_mono hφK)
  have hvalue (x : E) (hx : x ∈ K) : U (e x) = φ x :=
    coordinateExtension_comp_apply e φ (hKs hx)
  have hderiv (x : E) (hx : x ∈ K) :
      fderiv ℝ (fun y => U (e y)) x = fderiv ℝ (φ : E → ℝ) x :=
    (EnergyTest.ofCoordinates_comp_eventuallyEq (D := g.leviCivitaData)
      e hei φ φ.smooth.contDiff φ.hasCompactSupport
        (fun y hy => ⟨hKs (hφK hy), mem_univ _⟩) (hKs hx)).fderiv_eq
  have hL2 : (∫ y, U y * U y ∂g.volumeMeasure) =
      ∫ x in K, φ x ^ 2 * g.pullbackVolumeDensity e x := by
    calc
      _ = ∫ y in e '' K, U y * U y ∂g.volumeMeasure := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy
        rw [image_eq_zero_of_notMem_tsupport (fun ht => hy (hUimage ht)), zero_mul]
      _ = ∫ x in K, U (e x) * U (e x) * g.pullbackVolumeDensity e x :=
        integral_compact_image_eq_pullback_density (g := g) e he hei hK hKs
          (U.smooth.continuous.measurable.mul U.smooth.continuous.measurable)
      _ = _ := setIntegral_congr_fun hK.measurableSet fun x hx => by rw [hvalue x hx, pow_two]
  have hgrad : (∫ y, g.inner y (g.leviCivitaData.gradient U y)
      (g.leviCivitaData.gradient U y) ∂g.volumeMeasure) =
      ∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j *
        fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single j 1) *
        fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1) := by
    rw [integral_gradient_eq_compact_coordinates e he hei hK hKs U U hUimage]
    apply setIntegral_congr_fun hK.measurableSet
    intro x hx
    change g.inner (e x) (g.leviCivitaData.gradient U (e x))
      (g.leviCivitaData.gradient U (e x)) * g.pullbackVolumeDensity e x = _
    rw [mul_comm, density_mul_inner_gradient_eq_sum_divergenceCoefficients e he hei U U
      (hKs hx), hderiv x hx]
  have hφ2i : Integrable (fun x : E => φ x ^ 2) volume := by
    simpa only [native_euclideanMetric_volumeMeasure] using φ.memLp.integrable_sq
  have hpoint (x : E) (hx : x ∈ K) :
      φ x ^ 2 * g.pullbackVolumeDensity e x +
        (∑ i, ∑ j, divergenceCoefficients g e x i j *
          fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single j 1) *
          fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1)) ≤
        C * (φ x ^ 2 + G x) := by
    have h1 := mul_le_mul_of_nonneg_left (hρC x hx) (sq_nonneg (φ x))
    have h2 := (coordinate_quadratic_le_absSum (divergenceCoefficients g e x) φ x).trans
      (mul_le_mul_of_nonneg_right (hAC x hx) (hGnonneg x))
    calc
      _ ≤ φ x ^ 2 * C + C * G x := add_le_add h1 h2
      _ = _ := by ring
  have hcoord : ContinuousOn (fun x : E =>
      ∑ i, ∑ j, divergenceCoefficients g e x i j *
        fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single j 1) *
        fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1)) K := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact (((contDiffOn_divergenceCoefficients (g := g) e he hei i j).continuousOn.mono hKs).mul (((φ.smooth.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn)).mul
        (((φ.smooth.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn)
  have hsq : ‖U‖ ^ 2 ≤ C * ‖φ‖ ^ 2 := by
    calc
      _ = (∫ x in K, φ x ^ 2 * g.pullbackVolumeDensity e x) +
          ∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j *
            fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single j 1) *
            fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1) := by
        rw [U.norm_sq, energyInner, hL2, hgrad]
      _ = ∫ x in K, φ x ^ 2 * g.pullbackVolumeDensity e x +
          (∑ i, ∑ j, divergenceCoefficients g e x i j *
            fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single j 1) *
            fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1)) :=
        (integral_add (((φ.smooth.continuous.pow 2).continuousOn.mul hρ).integrableOn_compact hK) (hcoord.integrableOn_compact hK)).symm
      _ ≤ ∫ x in K, C * (φ x ^ 2 + G x) :=
        setIntegral_mono_on ((((φ.smooth.continuous.pow 2).continuousOn.mul hρ).add hcoord).integrableOn_compact hK)
          ((hφ2i.add hGi).const_mul C).integrableOn hK.measurableSet hpoint
      _ = C * ∫ x in K, φ x ^ 2 + G x := integral_const_mul _ _
      _ ≤ C * ∫ x : E, φ x ^ 2 + G x :=
        mul_le_mul_of_nonneg_left
          (setIntegral_le_integral (hφ2i.add hGi)
            (Eventually.of_forall fun x => add_nonneg (sq_nonneg _) (hGnonneg x))) hC.le
      _ = C * ‖φ‖ ^ 2 := by
        rw [integral_add hφ2i hGi, φ.norm_sq, energyInner,
          native_euclideanMetric_volumeMeasure]
        simp only [pow_two]
        rfl
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt hC.le] using hsq

#print axioms exists_nativeCoordinateEnergyTest_bound

end Yamabe3.Analysis.SpherePolar
