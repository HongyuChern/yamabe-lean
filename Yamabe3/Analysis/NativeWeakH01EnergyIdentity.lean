import Yamabe3.Analysis.NativeWeakH01CompletionCore
import PoincareLib.Geometry.Riemannian.Coordinates.Harmonic.WeakDirichlet

/-!
# The same coordinate weak derivatives in the native completion

The input is a sequence of literal smooth functions with strong L2
convergence of its values and of all three coordinate derivatives.  The
result identifies the native completed gradient pairing with precisely
these derivative limits.  No weak derivative is chosen a second time.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Filter MeasureTheory PoincareMT UniformSpace
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal

namespace Yamabe3.Analysis.SpherePolar

open PoincareMT.LeviCivitaData.Dirichlet

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "D" => nativeWeakEuclideanD

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private def weakEnergyTestNormedSpace (O : Set E) :
    NormedSpace ℝ (EnergyTest D O) := inferInstance
private def weakEnergyNormedSpace (O : Set E) :
    NormedSpace ℝ (H1Zero D O) := inferInstance
attribute [local instance] weakEnergyTestNormedSpace weakEnergyNormedSpace

/-- The true native gradient form is the sum of the three literal
coordinate derivative pairings, with no change of source or of metric. -/
theorem nativeEuclidean_test_gradient_pairing {O : Set E}
    (φ η : EnergyTest D O) :
    gradientEnergy D O (φ : H1Zero D O) (η : H1Zero D O) =
      ∑ i : Fin 3, ∫ x in O,
        fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1) *
          fderiv ℝ (η : E → ℝ) x (EuclideanSpace.single i 1) := by
  rw [gradientEnergy_coe, native_euclideanMetric_volumeMeasure]
  have hi (i : Fin 3) : Integrable (fun x : E =>
      fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1) *
        fderiv ℝ (η : E → ℝ) x (EuclideanSpace.single i 1)) volume :=
    (nativeEuclidean_test_derivative_memLp O φ i).integrable_mul
      (nativeEuclidean_test_derivative_memLp O η i)
  calc
    _ = ∫ x : E, ∑ i : Fin 3,
        fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1) *
          fderiv ℝ (η : E → ℝ) x (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change @inner ℝ E _ (nativeWeakEuclideanD.gradient (φ : E → ℝ) x)
          (nativeWeakEuclideanD.gradient (η : E → ℝ) x : E) =
            ∑ i : Fin 3, fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1) *
              fderiv ℝ (η : E → ℝ) x (EuclideanSpace.single i 1)
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp only [dotProduct, Pi.star_apply, star_trivial]
        apply Finset.sum_congr rfl
        intro i _
        rw [nativeEuclidean_gradient_component, nativeEuclidean_gradient_component]
        ring
    _ = ∑ i : Fin 3, ∫ x : E,
        fderiv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1) *
          fderiv ℝ (η : E → ℝ) x (EuclideanSpace.single i 1) :=
      integral_finsetSum _ (fun i _ => hi i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz := fderiv_of_notMem_tsupport ℝ
        (show x ∉ tsupport (φ : E → ℝ) from fun ht => hx (φ.support_subset ht))
      simp only [hz, ContinuousLinearMap.zero_apply, zero_mul]

/-- Strong convergence in the original weak H1 realization converges to
the unique native completion element representing the same function. -/
theorem nativeEuclidean_approximation_tendsto_to_rep
    {O : Set E} (hO : IsOpen O)
    (φ : ℕ → EnergyTest D O) (u : E → ℝ) (du : E → E)
    (hu : MemLp u 2 (volume.restrict O))
    (hdu : ∀ i : Fin 3, MemLp (fun x => du x i) 2 (volume.restrict O))
    (hv : Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2
      (volume.restrict O)) atTop (𝓝 0))
    (hd : ∀ i : Fin 3, Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (φ n : E → ℝ) x (EuclideanSpace.single i 1) - du x i)
      2 (volume.restrict O)) atTop (𝓝 0))
    (z : H1Zero D O)
    (hzrep : (toL2 D O z : E → ℝ) =ᵐ[volume] O.indicator u) :
    Tendsto (fun n => (φ n : H1Zero D O)) atTop (𝓝 z) := by
  have hC := nativeEuclidean_test_cauchy_of_weak_approximation hO φ u du hu hdu hv hd
  obtain ⟨z₁, hz₁⟩ := cauchySeq_tendsto_of_complete
    ((Completion.uniformContinuous_coe _).comp_cauchySeq hC)
  have hnative : Tendsto (fun n => toL2 D O (φ n : H1Zero D O))
      atTop (𝓝 (toL2 D O z₁)) := (toL2 D O).continuous.tendsto z₁ |>.comp hz₁
  have hmem : MemLp (O.indicator u) 2
      (RiemannianMetric.euclideanMetric 3).volumeMeasure := by
    rw [native_euclideanMetric_volumeMeasure]
    exact (memLp_indicator_iff_restrict hO.measurableSet).mpr hu
  have hvalue : Tendsto (fun n => (φ n).memLp.toLp (φ n : E → ℝ))
      atTop (𝓝 (hmem.toLp (O.indicator u))) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
    have heq (n : ℕ) : (fun x => φ n x - O.indicator u x) =
        O.indicator (fun x => φ n x - u x) := by
      funext x
      by_cases hx : x ∈ O
      · simp [hx]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx,
          image_eq_zero_of_notMem_tsupport (fun ht => hx ((φ n).support_subset ht)), sub_zero]
    change Tendsto (fun n => eLpNorm (fun x => φ n x - O.indicator u x) 2
      (RiemannianMetric.euclideanMetric 3).volumeMeasure) atTop (𝓝 0)
    simpa only [native_euclideanMetric_volumeMeasure, heq,
      eLpNorm_indicator_eq_eLpNorm_restrict hO.measurableSet] using hv
  have hz₁L2 : toL2 D O z₁ = hmem.toLp (O.indicator u) := by
    apply tendsto_nhds_unique hnative
    convert hvalue using 1
    funext n
    rw [toL2_coe]
    rfl
  have hzL2 : toL2 D O z = hmem.toLp (O.indicator u) := by
    apply Lp.ext
    have hzrep' : (toL2 D O z : E → ℝ) =ᵐ[
        (RiemannianMetric.euclideanMetric 3).volumeMeasure] O.indicator u := by
      simpa only [native_euclideanMetric_volumeMeasure] using hzrep
    exact hzrep'.trans hmem.coeFn_toLp.symm
  have heq : z₁ = z := toL2_injective (hz₁L2.trans hzL2.symm)
  simpa only [heq, Function.comp_def] using! hz₁

/-- The native completed gradient pairs with the very same weak gradient
which appears in the original strong H1 approximation. -/
theorem nativeEuclidean_gradient_pairing_of_weak_approximation
    {O : Set E} (hO : IsOpen O)
    (φ : ℕ → EnergyTest D O) (u : E → ℝ) (du : E → E)
    (hu : MemLp u 2 (volume.restrict O))
    (hdu : ∀ i : Fin 3, MemLp (fun x => du x i) 2 (volume.restrict O))
    (hv : Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2
      (volume.restrict O)) atTop (𝓝 0))
    (hd : ∀ i : Fin 3, Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (φ n : E → ℝ) x (EuclideanSpace.single i 1) - du x i)
      2 (volume.restrict O)) atTop (𝓝 0))
    (z : H1Zero D O)
    (hzrep : (toL2 D O z : E → ℝ) =ᵐ[volume] O.indicator u)
    (η : EnergyTest D O) :
    gradientEnergy D O z (η : H1Zero D O) =
      ∑ i : Fin 3, ∫ x in O, du x i *
        fderiv ℝ (η : E → ℝ) x (EuclideanSpace.single i 1) := by
  have hz := nativeEuclidean_approximation_tendsto_to_rep
    hO φ u du hu hdu hv hd z hzrep
  have hleft : Tendsto (fun n => gradientEnergy D O
      (φ n : H1Zero D O) (η : H1Zero D O)) atTop
      (𝓝 (gradientEnergy D O z (η : H1Zero D O))) := by
    exact (show Continuous (fun v : H1Zero D O =>
      gradientEnergy D O v (η : H1Zero D O)) by fun_prop).continuousAt.tendsto.comp hz
  have hterm (i : Fin 3) : Tendsto (fun n => ∫ x in O,
      fderiv ℝ (φ n : E → ℝ) x (EuclideanSpace.single i 1) *
        fderiv ℝ (η : E → ℝ) x (EuclideanSpace.single i 1)) atTop
      (𝓝 (∫ x in O, du x i *
        fderiv ℝ (η : E → ℝ) x (EuclideanSpace.single i 1))) := by
    let p (n : ℕ) := ((nativeEuclidean_test_derivative_memLp O (φ n) i).restrict O).toLp
      (fun x => fderiv ℝ (φ n : E → ℝ) x (EuclideanSpace.single i 1))
    let q := ((nativeEuclidean_test_derivative_memLp O η i).restrict O).toLp
      (fun x => fderiv ℝ (η : E → ℝ) x (EuclideanSpace.single i 1))
    have hp : Tendsto p atTop (𝓝 ((hdu i).toLp (fun x => du x i))) :=
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr (hd i)
    have hpq := hp.inner (𝕜 := ℝ) tendsto_const_nhds (g := fun _ : ℕ => q)
    have hint (f h : E → ℝ) (hf : MemLp f 2 (volume.restrict O))
        (hh : MemLp h 2 (volume.restrict O)) :
        inner ℝ (hf.toLp f) (hh.toLp h) = ∫ x in O, f x * h x := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp, hh.coeFn_toLp] with x hfx hhx
      simp only [hfx, hhx, RCLike.inner_apply, conj_trivial]
      ring
    simpa only [p, q, hint] using hpq
  have hright := tendsto_finset_sum Finset.univ (fun i _ => hterm i)
  have hright' : Tendsto (fun n => gradientEnergy D O
      (φ n : H1Zero D O) (η : H1Zero D O)) atTop
      (𝓝 (∑ i : Fin 3, ∫ x in O, du x i *
        fderiv ℝ (η : E → ℝ) x (EuclideanSpace.single i 1))) := by
    simpa only [nativeEuclidean_test_gradient_pairing] using hright
  exact tendsto_nhds_unique hleft hright'

#print axioms nativeEuclidean_test_gradient_pairing
#print axioms nativeEuclidean_approximation_tendsto_to_rep
#print axioms nativeEuclidean_gradient_pairing_of_weak_approximation

end Yamabe3.Analysis.SpherePolar
