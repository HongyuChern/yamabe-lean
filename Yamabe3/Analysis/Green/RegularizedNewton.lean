import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-!
# Smooth Euclidean Newton regularization in dimension three

This file proves analytic facts about the genuine Euclidean Laplacian and Lebesgue
measure.  It does not assume a Green function or a distributional point-source
identity on a manifold.  The latter requires a separate coordinate transport and
residual estimate.
-/

noncomputable section

open Filter Set MeasureTheory InnerProductSpace Laplacian
open scoped Topology RealInnerProductSpace

namespace Yamabe3.RegularizedNewton

abbrev E := EuclideanSpace ℝ (Fin 3)

/-- A smooth approximation of the Newton potential `‖x‖⁻¹`. -/
def potential (ε : ℝ) (x : E) : ℝ :=
  (‖x‖ ^ 2 + ε ^ 2) ^ (-(1 / 2 : ℝ))

/-- The positive density obtained by applying the negative Euclidean Laplacian. -/
def kernel (ε : ℝ) (x : E) : ℝ :=
  3 * ε ^ 2 * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ))

lemma normSq_add_sq_pos {ε : ℝ} (hε : 0 < ε) (x : E) :
    0 < ‖x‖ ^ 2 + ε ^ 2 :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)

lemma hasFDerivAt_radial_rpow {ε : ℝ} (hε : 0 < ε) (p : ℝ) (x : E) :
    HasFDerivAt (fun y : E => (‖y‖ ^ 2 + ε ^ 2) ^ p)
      ((2 * p * (‖x‖ ^ 2 + ε ^ 2) ^ (p - 1)) • innerSL ℝ x) x := by
  convert! (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (ε ^ 2)).rpow_const (p := p)
    (Or.inl (normSq_add_sq_pos hε x).ne')) using 0
  simp_rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num
  ring_nf
  simp only [add_comm]

theorem contDiff_potential {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ⊤ (potential ε) := by
  exact ((contDiff_id.norm_sq ℝ).add contDiff_const).rpow_const_of_ne
    (fun x => (normSq_add_sq_pos hε x).ne')

theorem hasFDerivAt_potential {ε : ℝ} (hε : 0 < ε) (x : E) :
    HasFDerivAt (potential ε)
      (-(‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) • innerSL ℝ x) x := by
  convert! hasFDerivAt_radial_rpow hε (-(1 / 2 : ℝ)) x using 1
  norm_num [potential]

theorem fderiv_potential {ε : ℝ} (hε : 0 < ε) (x : E) :
    fderiv ℝ (potential ε) x =
      -(‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) • innerSL ℝ x :=
  (hasFDerivAt_potential hε x).fderiv

theorem second_derivative_potential {ε : ℝ} (hε : 0 < ε) (x v w : E) :
    iteratedFDeriv ℝ 2 (potential ε) x ![v, w] =
      3 * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) * ⟪x, v⟫ * ⟪x, w⟫ -
        (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) * ⟪v, w⟫ := by
  have hs : HasFDerivAt (fun y : E => -(‖y‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)))
      ((3 * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ))) • innerSL ℝ x) x := by
    convert! (hasFDerivAt_radial_rpow hε (-(3 / 2 : ℝ)) x).neg using 1
    norm_num
  have hgrad := hs.smul ((innerSL ℝ (E := E)).hasFDerivAt)
  rw [Pi.smul_def'] at hgrad
  have hfun : fderiv ℝ (potential ε) =
      (fun y : E => -(‖y‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) • innerSL ℝ y) := by
    funext y
    exact fderiv_potential hε y
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hfun]
  rw [hgrad.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]
  change -(‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) * ⟪v, w⟫ +
      (3 * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) * ⟪x, v⟫) * ⟪x, w⟫ = _
  ring

theorem negative_laplacian_potential {ε : ℝ} (hε : 0 < ε) (x : E) :
    -(Δ (potential ε) x) = kernel ε x := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (potential ε) b]
  have hdiag (i : Fin 3) : iteratedFDeriv ℝ 2 (potential ε) x ![b i, b i] =
      (3 * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ))) * ⟪x, b i⟫ ^ 2 -
        (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) := by
    rw [second_derivative_potential hε]
    simp only [b.inner_eq_ite, ite_true, mul_one]
    ring
  simp_rw [hdiag]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, b.sum_sq_inner_left,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hp : (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) =
      (‖x‖ ^ 2 + ε ^ 2) * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) := by
    calc
      _ = (‖x‖ ^ 2 + ε ^ 2) ^ ((1 : ℝ) + -(5 / 2 : ℝ)) := by norm_num
      _ = _ := by rw [Real.rpow_add (normSq_add_sq_pos hε x), Real.rpow_one]
  rw [hp]
  unfold kernel
  ring

theorem kernel_nonneg {ε : ℝ} (hε : 0 < ε) (x : E) : 0 ≤ kernel ε x := by
  unfold kernel
  positivity

/-- Radial mass primitive, before the Euclidean sphere area factor `4 * π`. -/
def radialMass (ε r : ℝ) : ℝ := r ^ 3 * (r ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ))

lemma realSq_add_sq_pos {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    0 < r ^ 2 + ε ^ 2 :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)

theorem hasDerivAt_radialMass {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    HasDerivAt (radialMass ε)
      (r ^ 2 * (3 * ε ^ 2 * (r ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)))) r := by
  have h := ((hasDerivAt_id r).pow 3).mul
    ((((hasDerivAt_id r).pow 2).add_const (ε ^ 2)).rpow_const (p := -(3 / 2 : ℝ))
      (Or.inl (realSq_add_sq_pos hε r).ne'))
  have hp : (r ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) =
      (r ^ 2 + ε ^ 2) * (r ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) := by
    calc
      _ = (r ^ 2 + ε ^ 2) ^ ((1 : ℝ) + -(5 / 2 : ℝ)) := by norm_num
      _ = _ := by rw [Real.rpow_add (realSq_add_sq_pos hε r), Real.rpow_one]
  convert! h using 1
  norm_num
  rw [hp]
  ring

theorem radialMass_eq_ratio {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    radialMass ε r = (r ^ 2 / (r ^ 2 + ε ^ 2)) ^ (3 / 2 : ℝ) := by
  rw [radialMass, Real.div_rpow (sq_nonneg _) (realSq_add_sq_pos hε r).le,
    ← Real.rpow_natCast_mul hr.le 2 (3 / 2 : ℝ), Real.rpow_neg (realSq_add_sq_pos hε r).le]
  norm_num
  rfl

theorem tendsto_radialMass_atTop {ε : ℝ} (hε : 0 < ε) :
    Tendsto (radialMass ε) atTop (𝓝 1) := by
  have hz : Tendsto (fun r : ℝ => ε ^ 2 / r ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  have ht : Tendsto (fun r : ℝ => 1 / (1 + ε ^ 2 / r ^ 2)) atTop (𝓝 1) := by
    convert! tendsto_const_nhds.div (tendsto_const_nhds.add hz) (by norm_num : (1 : ℝ) + 0 ≠ 0) using 1
    norm_num
  have hpow := ht.rpow_const (p := (3 / 2 : ℝ)) (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  simp only [Real.one_rpow] at hpow
  apply hpow.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [radialMass_eq_ratio hε hr]
  congr 1
  field_simp

theorem integrable_radial_kernel {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun r : ℝ => r ^ 2 * (3 * ε ^ 2 * (r ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ))))
      (Ioi 0) := by
  exact integrableOn_Ioi_deriv_of_nonneg' (fun r _ => hasDerivAt_radialMass hε r)
    (fun r _ => by positivity) (tendsto_radialMass_atTop hε)

theorem integral_radial_kernel {ε : ℝ} (hε : 0 < ε) :
    (∫ r in Ioi (0 : ℝ), r ^ 2 * (3 * ε ^ 2 * (r ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)))) = 1 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun r (_ : r ∈ Ici (0 : ℝ)) => hasDerivAt_radialMass hε r)
    (fun r (_ : r ∈ Ioi (0 : ℝ)) => by positivity) (tendsto_radialMass_atTop hε)
  simpa [radialMass] using h

theorem integrable_kernel {ε : ℝ} (hε : 0 < ε) : Integrable (kernel ε) := by
  unfold kernel
  apply (integrable_fun_norm_addHaar (volume : Measure E)
    (f := fun r : ℝ => 3 * ε ^ 2 * (r ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)))).2
  simpa [kernel] using integrable_radial_kernel hε

theorem integral_kernel {ε : ℝ} (hε : 0 < ε) :
    (∫ x : E, kernel ε x) = 4 * Real.pi := by
  unfold kernel
  rw [integral_fun_norm_addHaar (volume : Measure E)
    (fun r : ℝ => 3 * ε ^ 2 * (r ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)))]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub,
    smul_eq_mul, nsmul_eq_mul, integral_radial_kernel hε, mul_one]
  rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
  norm_num only [ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

theorem contDiff_kernel {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ⊤ (kernel ε) := by
  exact contDiff_const.mul
    (((contDiff_id.norm_sq ℝ).add contDiff_const).rpow_const_of_ne
      (fun x => (normSq_add_sq_pos hε x).ne'))

theorem kernel_smul {ε : ℝ} (hε : 0 < ε) (x : E) :
    kernel ε (ε • x) = (ε ^ 3)⁻¹ * kernel 1 x := by
  have hs : ‖ε • x‖ ^ 2 + ε ^ 2 = ε ^ 2 * (‖x‖ ^ 2 + 1) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    ring
  have hp : (ε ^ 2) ^ (-(5 / 2 : ℝ)) = (ε ^ 5)⁻¹ := by
    rw [← Real.rpow_natCast_mul hε.le 2 (-(5 / 2 : ℝ))]
    norm_num [Real.rpow_neg hε.le]
  unfold kernel
  rw [hs, Real.mul_rpow (sq_nonneg ε) (by positivity), hp]
  norm_num
  field_simp

theorem integral_kernel_mul_eq_rescaled {ε : ℝ} (hε : 0 < ε) (f : E → ℝ) :
    (∫ x : E, kernel ε x * f x) = ∫ y : E, kernel 1 y * f (ε • y) := by
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure E)
    (fun x => kernel ε x * f x) ε (hR := hε.le)
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at h
  simp_rw [kernel_smul hε, mul_assoc] at h
  rw [integral_const_mul] at h
  exact (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ hε.ne')) h).symm

theorem tendsto_rescaled_kernel_test {f : E → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun ε : ℝ => ∫ y : E, kernel 1 y * f (ε • y)) (𝓝 0)
      (𝓝 (4 * Real.pi * f 0)) := by
  have hdom : Tendsto (fun ε : ℝ => ∫ y : E, kernel 1 y * f (ε • y)) (𝓝 0)
      (𝓝 (∫ y : E, kernel 1 y * f 0)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun y : E => kernel 1 y * C)
    · apply Filter.Eventually.of_forall
      intro ε
      apply Continuous.aestronglyMeasurable
      have hk := (contDiff_kernel (by norm_num : (0 : ℝ) < 1)).continuous
      fun_prop
    · exact Filter.Eventually.of_forall (fun ε => Filter.Eventually.of_forall (fun y => by
        rw [norm_mul, Real.norm_eq_abs (kernel 1 y), abs_of_nonneg (kernel_nonneg (by norm_num) y)]
        exact mul_le_mul_of_nonneg_left (hC _) (kernel_nonneg (by norm_num) y)))
    · exact (integrable_kernel (by norm_num : (0 : ℝ) < 1)).mul_const C
    · apply Filter.Eventually.of_forall
      intro y
      have hy : Tendsto (fun ε : ℝ => ε • y) (𝓝 0) (𝓝 (0 : E)) := by
        have hc : Continuous (fun ε : ℝ => ε • y) := by fun_prop
        simpa using hc.tendsto (0 : ℝ)
      exact tendsto_const_nhds.mul (hf.continuousAt.tendsto.comp hy)
  simpa only [integral_mul_const, integral_kernel (by norm_num : (0 : ℝ) < 1)] using hdom

/-- The regularized densities converge to `4 * π` times point evaluation.
The result is for actual Lebesgue integrals of bounded continuous test functions. -/
theorem tendsto_kernel_test {f : E → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun ε : ℝ => ∫ x : E, kernel ε x * f x) (𝓝[>] 0)
      (𝓝 (4 * Real.pi * f 0)) := by
  apply ((tendsto_rescaled_kernel_test hf hC).mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_kernel_mul_eq_rescaled hε f).symm

/-- The scalar radial domination used in the local parametrix error estimates. -/
theorem radial_rpow_le_inv_pow (ε : ℝ) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (r ^ 2 + ε ^ 2) ^ (-((n : ℝ) / 2)) ≤ (r ^ n)⁻¹ := by
  calc
    _ ≤ (r ^ 2) ^ (-((n : ℝ) / 2)) :=
      Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hr)
        (le_add_of_nonneg_right (sq_nonneg ε)) (neg_nonpos.mpr (by positivity))
    _ = _ := by
      rw [← Real.rpow_natCast_mul hr.le 2 (-((n : ℝ) / 2))]
      norm_num only [Nat.cast_ofNat]
      have he : (2 : ℝ) * (-((n : ℝ) / 2)) = -(n : ℝ) := by ring
      rw [he, Real.rpow_neg hr.le, Real.rpow_natCast]

theorem potential_nonneg (ε : ℝ) (x : E) : 0 ≤ potential ε x := by
  unfold potential
  positivity

theorem potential_le_inv_norm (ε : ℝ) {x : E} (hx : x ≠ 0) :
    potential ε x ≤ ‖x‖⁻¹ := by
  simpa [potential] using radial_rpow_le_inv_pow ε (norm_pos_iff.mpr hx) 1

theorem tendsto_potential {x : E} (hx : x ≠ 0) :
    Tendsto (fun ε : ℝ => potential ε x) (𝓝 0) (𝓝 ‖x‖⁻¹) := by
  have hs : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hbase : Tendsto (fun ε : ℝ => ‖x‖ ^ 2 + ε ^ 2) (𝓝 0) (𝓝 (‖x‖ ^ 2)) := by
    have hc : Continuous (fun ε : ℝ => ‖x‖ ^ 2 + ε ^ 2) := by fun_prop
    simpa using hc.tendsto (0 : ℝ)
  have h := hbase.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hs.ne')
  have hp : (‖x‖ ^ 2) ^ (-(1 / 2 : ℝ)) = ‖x‖⁻¹ := by
    rw [← Real.rpow_natCast_mul (norm_nonneg x) 2 (-(1 / 2 : ℝ))]
    norm_num
    exact Real.rpow_neg_one _
  simpa only [potential, hp] using h

theorem norm_fderiv_potential_le {ε : ℝ} (hε : 0 < ε) {x : E} (hx : x ≠ 0) :
    ‖fderiv ℝ (potential ε) x‖ ≤ (‖x‖ ^ 2)⁻¹ := by
  rw [fderiv_potential hε, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (Real.rpow_pos_of_pos (normSq_add_sq_pos hε x) _), innerSL_apply_norm]
  have h := radial_rpow_le_inv_pow ε (norm_pos_iff.mpr hx) 3
  have he : (‖x‖ ^ 3)⁻¹ * ‖x‖ = (‖x‖ ^ 2)⁻¹ := by
    field_simp
  calc
    _ ≤ (‖x‖ ^ 3)⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := he

theorem norm_second_derivative_potential_le {ε : ℝ} (hε : 0 < ε)
    {x : E} (hx : x ≠ 0) (v w : E) :
    ‖iteratedFDeriv ℝ 2 (potential ε) x ![v, w]‖ ≤
      4 * (‖x‖ ^ 3)⁻¹ * ‖v‖ * ‖w‖ := by
  have hp5 : 0 ≤ (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) := by positivity
  have hp3 : 0 ≤ (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) := by positivity
  have h5 := radial_rpow_le_inv_pow ε (norm_pos_iff.mpr hx) 5
  have h3 := radial_rpow_le_inv_pow ε (norm_pos_iff.mpr hx) 3
  have hfirst : ‖3 * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) * ⟪x, v⟫ * ⟪x, w⟫‖ ≤
      3 * (‖x‖ ^ 5)⁻¹ * (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖) := by
    simp only [norm_mul, Real.norm_ofNat, Real.norm_of_nonneg hp5]
    gcongr
    · exact h5
    · exact norm_inner_le_norm x v
    · exact norm_inner_le_norm x w
  have hsecond : ‖(‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) * ⟪v, w⟫‖ ≤
      (‖x‖ ^ 3)⁻¹ * (‖v‖ * ‖w‖) := by
    simp only [norm_mul, Real.norm_of_nonneg hp3]
    gcongr
    · exact h3
    · exact norm_inner_le_norm v w
  rw [second_derivative_potential hε]
  calc
    _ ≤ ‖3 * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) * ⟪x, v⟫ * ⟪x, w⟫‖ +
        ‖(‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) * ⟪v, w⟫‖ := norm_sub_le _ _
    _ ≤ 3 * (‖x‖ ^ 5)⁻¹ * (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖) +
        (‖x‖ ^ 3)⁻¹ * (‖v‖ * ‖w‖) := add_le_add hfirst hsecond
    _ = _ := by
      field_simp [norm_ne_zero_iff.mpr hx]
      ring

end Yamabe3.RegularizedNewton
