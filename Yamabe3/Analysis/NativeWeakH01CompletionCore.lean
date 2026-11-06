import Yamabe3.Analysis.NativeEuclideanVolume
import PoincareLib.Geometry.Riemannian.Connection.Construction
import Yamabe3.Analysis.UniformElliptic.NativeL2SquareConvergence
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Support

/-!
# A weak H1-zero function in the original energy completion

The actual compact smooth approximants and their strong L2 limits are used with their actual
values and actual coordinate derivatives. Their energy is the native
Euclidean energy, with the already proved equality of native volume and
Lebesgue measure. The limit has precisely the zero extension of the input
function as its L2 representative. No boundary value is assigned to an
almost-everywhere representative.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Filter MeasureTheory PoincareMT UniformSpace
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal

namespace Yamabe3.Analysis.SpherePolar

open PoincareMT.LeviCivitaData.Dirichlet
open UniformElliptic

local notation "E" => EuclideanSpace ℝ (Fin 3)
abbrev nativeWeakEuclideanD := (RiemannianMetric.euclideanMetric 3).leviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private def weakCompletionTestNormedSpace (O : Set E) :
    NormedSpace ℝ (EnergyTest nativeWeakEuclideanD O) := inferInstance
private def weakCompletionNormedSpace (O : Set E) :
    NormedSpace ℝ (H1Zero nativeWeakEuclideanD O) := inferInstance
attribute [local instance] weakCompletionTestNormedSpace weakCompletionNormedSpace

/-- The gradient coordinates are the actual Frechet partial derivatives. -/
theorem nativeEuclidean_gradient_component (O : Set E)
    (φ : EnergyTest nativeWeakEuclideanD O) (x : E) (i : Fin 3) :
    WithLp.ofLp (nativeWeakEuclideanD.gradient φ x : E) i =
      fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1) := by
  have h := nativeWeakEuclideanD.inner_gradient (φ : E → ℝ) x (EuclideanSpace.single i 1)
  simpa only [RiemannianMetric.euclideanMetric_inner,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul,
    mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
    ContinuousLinearMap.comp_apply] using! h

theorem nativeEuclidean_test_derivative_memLp (O : Set E)
    (φ : EnergyTest nativeWeakEuclideanD O) (i : Fin 3) :
    MemLp (fun x => fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1))
      2 volume := by
  exact ((φ.smooth.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (φ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ)))

/-- There is no metric-comparison constant in the Euclidean energy
identity: all three coordinate derivative squares occur exactly once. -/
theorem nativeEuclidean_test_norm_sq (O : Set E) (φ : EnergyTest nativeWeakEuclideanD O) :
    ‖φ‖ ^ 2 = (∫ x : E, φ x ^ 2) +
      ∑ i : Fin 3, ∫ x : E,
        (fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1)) ^ 2 := by
  rw [EnergyTest.norm_sq, energyInner, native_euclideanMetric_volumeMeasure]
  congr 1
  · apply integral_congr_ae
    exact Eventually.of_forall fun x => (pow_two (φ x)).symm
  · rw [← integral_finsetSum _ (fun i _ => (nativeEuclidean_test_derivative_memLp O φ i).integrable_sq)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change @inner ℝ E _ (nativeWeakEuclideanD.gradient (φ : E → ℝ) x)
        (nativeWeakEuclideanD.gradient (φ : E → ℝ) x : E) =
          ∑ i : Fin 3, (fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1)) ^ 2
      rw [real_inner_self_eq_norm_sq,
        EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_congr rfl
      intro i _
      rw [nativeEuclidean_gradient_component]

theorem nativeEuclidean_test_norm_sq_restrict {O : Set E} (hO : MeasurableSet O)
    (φ : EnergyTest nativeWeakEuclideanD O) :
    ‖φ‖ ^ 2 = (∫ x in O, φ x ^ 2) +
      ∑ i : Fin 3, ∫ x in O,
        (fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1)) ^ 2 := by
  rw [nativeEuclidean_test_norm_sq]
  congr 1
  · symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (φ.support_subset ht)), zero_pow (by decide)]
  · apply Finset.sum_congr rfl
    intro i _
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hd := fderiv_of_notMem_tsupport ℝ
      (show x ∉ tsupport (φ : E → ℝ) from fun ht => hx (φ.support_subset ht))
    simp only [hd, ContinuousLinearMap.zero_apply, zero_pow (by decide : 2 ≠ 0)]

private def nativeEuclideanTestValue (O : Set E) (φ : EnergyTest nativeWeakEuclideanD O) :
    Lp ℝ 2 (volume.restrict O) :=
  (show MemLp (φ : E → ℝ) 2 (volume.restrict O) from
    (φ.smooth.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).restrict O).toLp φ

private def nativeEuclideanTestDerivative (O : Set E) (φ : EnergyTest nativeWeakEuclideanD O)
    (i : Fin 3) : Lp ℝ 2 (volume.restrict O) :=
  ((nativeEuclidean_test_derivative_memLp O φ i).restrict O).toLp
    (fun x => fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1))

private theorem nativeEuclidean_test_dist_sq {O : Set E} (hO : MeasurableSet O)
    (φ ψ : EnergyTest nativeWeakEuclideanD O) :
    dist φ ψ ^ 2 =
      ‖nativeEuclideanTestValue O φ - nativeEuclideanTestValue O ψ‖ ^ 2 +
        ∑ i : Fin 3, ‖nativeEuclideanTestDerivative O φ i -
          nativeEuclideanTestDerivative O ψ i‖ ^ 2 := by
  rw [dist_eq_norm, nativeEuclidean_test_norm_sq_restrict hO]
  have hfun : ((φ - ψ : EnergyTest nativeWeakEuclideanD O) : E → ℝ) =
      fun x => φ x - ψ x := rfl
  have hd (x : E) : fderiv ℝ ((φ - ψ : EnergyTest nativeWeakEuclideanD O) : E → ℝ) x =
      fderiv ℝ (φ : E → ℝ) x - fderiv ℝ (ψ : E → ℝ) x :=
    fderiv_sub (φ.smooth.contDiff.differentiable (by simp) x)
      (ψ.smooth.contDiff.differentiable (by simp) x)
  dsimp only [nativeEuclideanTestValue, nativeEuclideanTestDerivative]
  rw [native_norm_toLp_sub_sq_eq_integral_sq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [native_norm_toLp_sub_sq_eq_integral_sq]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simpa only [ContinuousLinearMap.sub_apply] using!
      congrArg (fun L : E →L[ℝ] ℝ => (L (EuclideanSpace.single i 1)) ^ 2) (hd x)

/-- Convergence of the same value and all actual weak derivatives makes
the original smooth tests Cauchy in the native energy norm. -/
theorem nativeEuclidean_test_cauchy_of_weak_approximation
    {O : Set E} (hO : IsOpen O)
    (φ : ℕ → EnergyTest nativeWeakEuclideanD O) (u : E → ℝ)
    (du : E → E) (hu : MemLp u 2 (volume.restrict O))
    (hdu : ∀ i : Fin 3, MemLp (fun x => du x i) 2 (volume.restrict O))
    (hv : Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2
      (volume.restrict O)) atTop (𝓝 0))
    (hd : ∀ i : Fin 3, Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (φ n : E → ℝ) x (EuclideanSpace.single i 1) - du x i)
      2 (volume.restrict O)) atTop (𝓝 0)) : CauchySeq φ := by
  have hval : Tendsto (fun n => nativeEuclideanTestValue O (φ n)) atTop
      (𝓝 (hu.toLp u)) := by
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr hv
  have hder (i : Fin 3) : Tendsto (fun n => nativeEuclideanTestDerivative O (φ n) i)
      atTop (𝓝 ((hdu i).toLp (fun x => du x i))) := by
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr (hd i)
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨Nv, hNv⟩ := Metric.cauchySeq_iff.mp hval.cauchySeq (ε / 3) (by positivity)
  have hDs : ∀ i : Fin 3, ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      dist (nativeEuclideanTestDerivative O (φ n) i)
        (nativeEuclideanTestDerivative O (φ m) i) < ε / 3 :=
    fun i => Metric.cauchySeq_iff.mp (hder i).cauchySeq (ε / 3) (by positivity)
  choose Nd hNd using hDs
  refine ⟨max Nv (Finset.univ.sup Nd), ?_⟩
  intro n hn m hm
  have hvnm : ‖nativeEuclideanTestValue O (φ n) - nativeEuclideanTestValue O (φ m)‖ < ε / 3 := by
    simpa only [dist_eq_norm] using
      hNv n ((le_max_left _ _).trans hn) m ((le_max_left _ _).trans hm)
  have hdnm (i : Fin 3) : ‖nativeEuclideanTestDerivative O (φ n) i -
      nativeEuclideanTestDerivative O (φ m) i‖ < ε / 3 := by
    rw [← dist_eq_norm]
    exact hNd i n ((Finset.le_sup (Finset.mem_univ i)).trans ((le_max_right _ _).trans hn))
      m ((Finset.le_sup (Finset.mem_univ i)).trans ((le_max_right _ _).trans hm))
  have hvbound : ‖nativeEuclideanTestValue O (φ n) - nativeEuclideanTestValue O (φ m)‖ ^ 2 ≤
      (ε / 3) ^ 2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hvnm.le
  have hdbound : (∑ i : Fin 3, ‖nativeEuclideanTestDerivative O (φ n) i -
      nativeEuclideanTestDerivative O (φ m) i‖ ^ 2) ≤ 3 * (ε / 3) ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin 3, (ε / 3) ^ 2 := Finset.sum_le_sum fun i _ =>
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hdnm i).le
      _ = _ := by simp
  have heq := nativeEuclidean_test_dist_sq hO.measurableSet (φ n) (φ m)
  nlinarith only [hε, heq, hvbound, hdbound, sq_pos_of_pos hε, dist_nonneg (x := φ n) (y := φ m)]

/-- The genuine weak H1-zero predicate gives an element of the original
completion with the same physical function, extended by zero outside O. -/
theorem exists_nativeEuclideanH01_of_approximation
    {O : Set E} (hO : IsOpen O) (u : E → ℝ) (du : E → E)
    (hu : MemLp u 2 (volume.restrict O))
    (hdu : ∀ i : Fin 3, MemLp (fun x => du x i) 2 (volume.restrict O))
    (ψ : ℕ → E → ℝ)
    (hψ : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n))
    (hc : ∀ n, HasCompactSupport (ψ n)) (hs : ∀ n, tsupport (ψ n) ⊆ O)
    (hv : Tendsto (fun n => eLpNorm (fun x => ψ n x - u x) 2
      (volume.restrict O)) atTop (𝓝 0))
    (hd : ∀ i : Fin 3, Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (ψ n) x (EuclideanSpace.single i 1) - du x i)
      2 (volume.restrict O)) atTop (𝓝 0)) :
    ∃ z : H1Zero nativeWeakEuclideanD O,
      (toL2 nativeWeakEuclideanD O z : E → ℝ) =ᵐ[volume] O.indicator u := by
  classical
  let φ (n : ℕ) : EnergyTest nativeWeakEuclideanD O :=
    ⟨ψ n, (hψ n).contMDiff, hc n, hs n⟩
  have hC := nativeEuclidean_test_cauchy_of_weak_approximation hO φ u du hu hdu hv hd
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete
    ((Completion.uniformContinuous_coe _).comp_cauchySeq hC)
  refine ⟨z, ?_⟩
  have hnative : Tendsto (fun n => toL2 nativeWeakEuclideanD O (φ n : H1Zero nativeWeakEuclideanD O))
      atTop (𝓝 (toL2 nativeWeakEuclideanD O z)) := (toL2 nativeWeakEuclideanD O).continuous.tendsto z |>.comp hz
  have hmem : MemLp (O.indicator u) 2
      (RiemannianMetric.euclideanMetric 3).volumeMeasure := by
    rw [native_euclideanMetric_volumeMeasure]
    exact (memLp_indicator_iff_restrict hO.measurableSet).mpr hu
  have hvalue : Tendsto (fun n => (φ n).memLp.toLp (φ n : E → ℝ))
      atTop (𝓝 (hmem.toLp (O.indicator u))) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
    have heq (n : ℕ) : (fun x => ψ n x - O.indicator u x) =
        O.indicator (fun x => ψ n x - u x) := by
      funext x
      by_cases hx : x ∈ O
      · simp [hx]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx,
          image_eq_zero_of_notMem_tsupport (fun ht => hx (hs n ht)), sub_zero]
    change Tendsto (fun n => eLpNorm (fun x => ψ n x - O.indicator u x) 2
      (RiemannianMetric.euclideanMetric 3).volumeMeasure) atTop (𝓝 0)
    simpa only [native_euclideanMetric_volumeMeasure,
      heq, eLpNorm_indicator_eq_eLpNorm_restrict hO.measurableSet] using hv
  have heq : toL2 nativeWeakEuclideanD O z = hmem.toLp (O.indicator u) := by
    apply tendsto_nhds_unique hnative
    convert hvalue using 1
    funext n
    rw [toL2_coe]
    rfl
  have hae : (toL2 nativeWeakEuclideanD O z : E → ℝ) =ᵐ[
      (RiemannianMetric.euclideanMetric 3).volumeMeasure] O.indicator u := by
    rw [heq]
    exact hmem.coeFn_toLp
  simpa only [native_euclideanMetric_volumeMeasure] using hae

#print axioms nativeEuclidean_test_cauchy_of_weak_approximation
#print axioms exists_nativeEuclideanH01_of_approximation

end Yamabe3.Analysis.SpherePolar
