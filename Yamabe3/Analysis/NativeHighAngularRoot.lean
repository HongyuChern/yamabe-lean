import Yamabe3.Analysis.NativeAngularProjections
import Yamabe3.Analysis.Sphere.NativeSphereEnergyGap

/-!
# The actual high angular square root from native H1 to native L2

Only genuine eigenvalues at least six are retained.  The finite energy
Bessel inequality of the actual round-sphere H1 completion supplies the
square-summable square-root coefficients; this is not a bounded generator
on all angular L2.  The coefficient is sqrt(lambda + 1/4) on the retained
spectrum and zero on every low mode.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter MeasureTheory PoincareMT
open scoped Topology lp RealInnerProductSpace

namespace Yamabe3.Analysis.Delaunay

open SphereSpectrum

private theorem angular_eigenvalue_nonneg (i : AngularIndex) :
    0 ≤ angularEigenvalue i := by
  rcases angularEigenvalue_zero_two_or_ge_six i with h | h | h
  · rw [h]
  · rw [h]; norm_num
  · linarith

private def highRootCoefficient (u : AngularH1) (i : AngularIndex) : ℝ :=
  if 6 ≤ angularEigenvalue i then
    nativeAngularRate i * inner ℝ (angularBasis i) (angularEmbedding u)
  else 0

private theorem highRootCoefficient_finite_bound (u : AngularH1)
    (s : Finset AngularIndex) :
    (∑ i ∈ s, ‖highRootCoefficient u i‖ ^ (2 : ℝ)) ≤ ‖u‖ ^ 2 := by
  apply le_trans _ (finite_angular_energy_bound u s)
  apply Finset.sum_le_sum
  intro i _
  rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  by_cases hi : 6 ≤ angularEigenvalue i
  · rw [highRootCoefficient, if_pos hi, mul_pow, nativeAngularRate_sq,
      max_eq_right hi]
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  · rw [highRootCoefficient, if_neg hi, zero_pow (by decide)]
    exact mul_nonneg (by linarith [angular_eigenvalue_nonneg i]) (sq_nonneg _)

private theorem highRootCoefficient_mem (u : AngularH1) :
    Memℓp (highRootCoefficient u) 2 := by
  apply memℓp_gen' (C := ‖u‖ ^ 2)
  intro s
  simpa only [ENNReal.toReal_ofNat] using highRootCoefficient_finite_bound u s

private def highRootCoordinates : AngularH1 →ₗ[ℝ] SpectralSpace AngularIndex where
  toFun u := ⟨highRootCoefficient u, highRootCoefficient_mem u⟩
  map_add' u v := by
    ext i
    change highRootCoefficient (u + v) i = highRootCoefficient u i + highRootCoefficient v i
    unfold highRootCoefficient
    rw [map_add, inner_add_right]
    split_ifs <;> ring
  map_smul' c u := by
    ext i
    change highRootCoefficient (c • u) i = c * highRootCoefficient u i
    unfold highRootCoefficient
    rw [map_smul, real_inner_smul_right]
    split_ifs <;> ring

private theorem highRootCoordinates_norm_le (u : AngularH1) :
    ‖highRootCoordinates u‖ ≤ ‖u‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    (norm_nonneg u)
  intro s
  change (∑ i ∈ s, ‖highRootCoefficient u i‖ ^ (2 : ENNReal).toReal) ≤
    ‖u‖ ^ (2 : ENNReal).toReal
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using highRootCoefficient_finite_bound u s

/-- The actual high spectral square root.  Its domain is the genuine
round-sphere H1 completion, not unrestricted angular L2. -/
def nativeHighAngularRootCLM : AngularH1 →L[ℝ] AngularL2 :=
  angularBasis.repr.symm.toLinearIsometry.toContinuousLinearMap.comp
    (highRootCoordinates.mkContinuous 1 (fun u => by
      simpa only [one_mul] using highRootCoordinates_norm_le u))

theorem nativeHighAngularRootCLM_coefficient (u : AngularH1) (i : AngularIndex) :
    inner ℝ (angularBasis i) (nativeHighAngularRootCLM u) =
      if 6 ≤ angularEigenvalue i then
        nativeAngularRate i * inner ℝ (angularBasis i) (angularEmbedding u)
      else 0 := by
  rw [← HilbertBasis.repr_apply_apply]
  change angularBasis.repr (angularBasis.repr.symm (highRootCoordinates u)) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem nativeHighAngularRootCLM_apply_norm_le (u : AngularH1) :
    ‖nativeHighAngularRootCLM u‖ ≤ ‖u‖ := by
  change ‖angularBasis.repr.symm (highRootCoordinates u)‖ ≤ ‖u‖
  rw [LinearIsometryEquiv.norm_map]
  exact highRootCoordinates_norm_le u

theorem nativeHighAngularRootCLM_norm_le : ‖nativeHighAngularRootCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using nativeHighAngularRootCLM_apply_norm_le u

theorem nativeHighAngularRootCLM_eq_rate_high_coefficient
    (u : AngularH1) (i : AngularIndex) :
    inner ℝ (angularBasis i) (nativeHighAngularRootCLM u) =
      nativeAngularRate i *
        inner ℝ (angularBasis i) (nativeHighProjection (angularEmbedding u)) := by
  rw [nativeHighAngularRootCLM_coefficient, nativeHighProjection,
    nativeAngularProjection_coefficient]
  split_ifs <;> simp

theorem nativeHighProjection_root (u : AngularH1) :
    nativeHighProjection (nativeHighAngularRootCLM u) = nativeHighAngularRootCLM u := by
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply]
  rw [nativeHighProjection, nativeAngularProjection_coefficient,
    nativeHighAngularRootCLM_coefficient]
  split_ifs <;> rfl

#print axioms nativeHighAngularRootCLM
#print axioms nativeHighAngularRootCLM_norm_le
#print axioms nativeHighAngularRootCLM_eq_rate_high_coefficient

end Yamabe3.Analysis.Delaunay
