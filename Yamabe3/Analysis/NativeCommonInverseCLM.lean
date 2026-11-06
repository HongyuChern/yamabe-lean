import Yamabe3.Analysis.NativeCanonicalCoefficients
import Yamabe3.Analysis.DelaunayWeightTwoSmallness

/-!
# The canonical full angular bounded linear inverse at weight two

The operator is the explicit sum of the actual high Hilbert convolution
fixed point and low future fixed point, composed with true native spectral
projections. The same operator has the uniform bound, source-difference
estimate and genuine smooth coefficient equations. No existentially
chosen solution is used to infer linearity.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory PoincareMT
open scoped Topology lp ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.SphereSpectrum

def delaunayPotentialBCF (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => (15 / 4) * v t ^ 4)
    (continuous_const.mul (hv.pow 4)) (15 / 4) (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (15 / 4) * v t ^ 4)]
      have hpow : v t ^ 4 ≤ 1 := pow_le_one₀ (hb t).1 (hb t).2
      linarith)

theorem delaunayPotentialBCF_integral_bound (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {κ : ℝ}
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * ((15 / 4) * v (t - s) ^ 4)) ≤ κ) :
    ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s *
      |delaunayPotentialBCF v hv hb (t - s)|) ≤ κ := by
  intro t
  convert hV t using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun s => by
    change spectralMajorant (5 / 2) (-2) s * |(15 / 4) * v (t - s) ^ 4| = _
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (15 / 4) * v (t - s) ^ 4)]

/-- The actual full inverse on conjugated native L2 time curves. -/
def nativeCommonWeightInverseCLM (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * ((15 / 4) * v (t - s) ^ 4)) ≤ κ) :
    (ℝ →ᵇ AngularL2) →L[ℝ] (ℝ →ᵇ AngularL2) :=
  (nativeIntegralAngularInverseCLM (by norm_num : |(-2 : ℝ)| < 5 / 2) hκ0 hκ1
    (delaunayPotentialBCF v hv hb) (delaunayPotentialBCF_integral_bound v hv hb hV)).comp
      (nativeProjectedSourceCLM (fun i => 6 ≤ angularEigenvalue i)) +
  (nativeLowAngularInverseCLM v hv hb 2 (by norm_num) (by norm_num)).comp
      (nativeProjectedSourceCLM (fun i => angularEigenvalue i < 6))

/-- The application formula exposes only the outer linear composition;
no proof step needs to unfold either contraction fixed point. -/
theorem nativeCommonWeightInverseCLM_apply (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * ((15 / 4) * v (t - s) ^ 4)) ≤ κ)
    (F : ℝ →ᵇ AngularL2) :
    nativeCommonWeightInverseCLM v hv hb hκ0 hκ1 hV F =
      nativeIntegralAngularInverseCLM (by norm_num : |(-2 : ℝ)| < 5 / 2) hκ0 hκ1
        (delaunayPotentialBCF v hv hb) (delaunayPotentialBCF_integral_bound v hv hb hV)
        (nativeProjectedSource (fun i => 6 ≤ angularEigenvalue i) F) +
      nativeLowAngularInverseCLM v hv hb 2 (by norm_num) (by norm_num)
        (nativeProjectedSource (fun i => angularEigenvalue i < 6) F) := by
  simp only [nativeCommonWeightInverseCLM, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, nativeProjectedSourceCLM_apply]

theorem nativeCommonWeightInverseCLM_apply_bound (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * ((15 / 4) * v (t - s) ^ 4)) ≤ κ)
    (F : ℝ →ᵇ AngularL2) :
    ‖nativeCommonWeightInverseCLM v hv hb hκ0 hκ1 hV F‖ ≤
      (4 / (9 * (1 - κ)) + 2) * ‖F‖ := by
  let FH := nativeProjectedSource (fun i => 6 ≤ angularEigenvalue i) F
  let FL := nativeProjectedSource (fun i => angularEigenvalue i < 6) F
  let V := delaunayPotentialBCF v hv hb
  have hVi := delaunayPotentialBCF_integral_bound v hv hb hV
  have hH : ‖nativeIntegralAngularInverseCLM (by norm_num : |(-2 : ℝ)| < 5 / 2)
      hκ0 hκ1 V hVi FH‖ ≤ (‖FH‖ / (9 / 4)) / (1 - κ) := by
    rw [nativeIntegralAngularInverseCLM_apply]
    convert nativeIntegralAngularInverse_norm_le (by norm_num : |(-2 : ℝ)| < 5 / 2)
      hκ0 hκ1 V hVi FH using 1 <;> norm_num
  have hL : ‖nativeLowAngularInverseCLM v hv hb 2 (by norm_num) (by norm_num) FL‖ ≤ 2 * ‖FL‖ := by
    convert nativeLowAngularInverseCLM_norm_le v hv hb (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (7 / 2 : ℝ) < 2 ^ 2) FL using 1 <;> ring
  have hFHn : ‖FH‖ ≤ ‖F‖ := nativeProjectedSource_norm_le _ F
  have hFLn : ‖FL‖ ≤ ‖F‖ := nativeProjectedSource_norm_le _ F
  rw [nativeCommonWeightInverseCLM_apply]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ (‖FH‖ / (9 / 4)) / (1 - κ) + 2 * ‖FL‖ := add_le_add hH hL
    _ ≤ (‖F‖ / (9 / 4)) / (1 - κ) + 2 * ‖F‖ := add_le_add
      (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hFHn (by norm_num))
        (sub_pos.mpr hκ1).le) (mul_le_mul_of_nonneg_left hFLn (by norm_num))
    _ = _ := by rw [div_mul_eq_div_div]; ring

theorem nativeCommonWeightInverseCLM_norm_le (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * ((15 / 4) * v (t - s) ^ 4)) ≤ κ) :
    ‖nativeCommonWeightInverseCLM v hv hb hκ0 hκ1 hV‖ ≤ 4 / (9 * (1 - κ)) + 2 := by
  have hden : 0 < 1 - κ := sub_pos.mpr hκ1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact nativeCommonWeightInverseCLM_apply_bound v hv hb hκ0 hκ1 hV

/-- A genuine source-difference estimate for the same actual inverse. -/
theorem nativeCommonWeightInverseCLM_weighted_difference (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * ((15 / 4) * v (t - s) ^ 4)) ≤ κ)
    (F H : ℝ →ᵇ AngularL2) (t : ℝ) :
    ‖Real.exp (-2 * t) • nativeCommonWeightInverseCLM v hv hb hκ0 hκ1 hV F t -
      Real.exp (-2 * t) • nativeCommonWeightInverseCLM v hv hb hκ0 hκ1 hV H t‖ ≤
      ((4 / (9 * (1 - κ)) + 2) * ‖F - H‖) * Real.exp (-2 * t) := by
  let R := nativeCommonWeightInverseCLM v hv hb hκ0 hκ1 hV
  have he : R F t - R H t = R (F - H) t := by rw [map_sub]; rfl
  change ‖Real.exp (-2 * t) • R F t - Real.exp (-2 * t) • R H t‖ ≤ _
  rw [← smul_sub, he, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-2 * t) * ((4 / (9 * (1 - κ)) + 2) * ‖F - H‖) :=
      mul_le_mul_of_nonneg_left ((BoundedContinuousFunction.norm_coe_le_norm _ t).trans
        (nativeCommonWeightInverseCLM_apply_bound v hv hb hκ0 hκ1 hV (F - H))) (Real.exp_pos _).le
    _ = _ := mul_comm _ _

private theorem modelJacobi_add_canonical {v f h : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (μ t : ℝ) :
    modelJacobi v μ (fun s => f s + h s) t = modelJacobi v μ f t + modelJacobi v μ h t := by
  have hfd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hhd : ContDiff ℝ ∞ (deriv h) := (contDiff_infty_iff_deriv.mp hh).2
  have hd : deriv (fun s => f s + h s) = fun s => deriv f s + deriv h s := by
    funext s
    exact ((hf.differentiable (by simp) s).hasDerivAt.add
      (hh.differentiable (by simp) s).hasDerivAt).deriv
  have hdd := ((hfd.differentiable (by simp) t).hasDerivAt.add
    (hhd.differentiable (by simp) t).hasDerivAt).deriv
  change deriv (fun s => deriv f s + deriv h s) t = deriv (deriv f) t + deriv (deriv h) t at hdd
  unfold modelJacobi
  rw [hd, hdd]
  ring

/-- Every actual coefficient of this exact canonical CLM solves the genuine
native angular equation. This identifies the curve used in the norm bound. -/
theorem nativeCommonWeightInverseCLM_weighted_coefficient {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * ((15 / 4) * v (t - s) ^ 4)) ≤ κ)
    (F : ℝ →ᵇ AngularL2)
    (hFs : ∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (F t))) (i : AngularIndex) :
    let u := fun t => inner ℝ (angularBasis i)
      (Real.exp (-2 * t) • nativeCommonWeightInverseCLM v hv.continuous hb hκ0 hκ1 hV F t)
    ContDiff ℝ ∞ u ∧ ∀ t, modelJacobi v (angularEigenvalue i) u t =
      Real.exp (-2 * t) * inner ℝ (angularBasis i) (F t) := by
  dsimp only
  let FH := nativeProjectedSource (fun i => 6 ≤ angularEigenvalue i) F
  let FL := nativeProjectedSource (fun i => angularEigenvalue i < 6) F
  let V := delaunayPotentialBCF v hv.continuous hb
  have hVi := delaunayPotentialBCF_integral_bound v hv.continuous hb hV
  let WH := nativeIntegralAngularInverseCLM (by norm_num : |(-2 : ℝ)| < 5 / 2) hκ0 hκ1 V hVi FH
  let WL := nativeLowAngularInverseCLM v hv.continuous hb 2 (by norm_num) (by norm_num) FL
  have hH := nativeIntegralAngularInverseCLM_weighted_coefficient hv
    (by norm_num : |(-2 : ℝ)| < 5 / 2) hκ0 hκ1 V hVi (fun _ => rfl) FH
    (nativeProjectedSource_coefficient_smooth _ F hFs)
    (fun j hj t => by rw [nativeProjectedSource_coefficient, if_neg (not_le.mpr hj)]) i
  have hL := nativeLowAngularInverseCLM_weighted_coefficient hv hb (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (7 / 2 : ℝ) < 2 ^ 2) FL
    (nativeProjectedSource_coefficient_smooth _ F hFs)
    (fun j hj t => by rw [nativeProjectedSource_coefficient, if_neg (not_lt.mpr hj)]) i
  dsimp only at hH hL
  have hcoef : (fun t => inner ℝ (angularBasis i)
      (Real.exp (-2 * t) • nativeCommonWeightInverseCLM v hv.continuous hb hκ0 hκ1 hV F t)) =
      fun t => Real.exp (-2 * t) * inner ℝ (angularBasis i) (WH t) +
        Real.exp (-2 * t) * inner ℝ (angularBasis i) (WL t) := by
    funext t
    rw [real_inner_smul_right, nativeCommonWeightInverseCLM_apply,
      BoundedContinuousFunction.add_apply, inner_add_right, mul_add]
  rw [hcoef]
  refine ⟨hH.1.add hL.1, fun t => ?_⟩
  rw [modelJacobi_add_canonical hH.1 hL.1, hH.2 t, hL.2 t, ← mul_add, ← inner_add_right]
  congr 2
  exact nativeHighProjection_add_low (F t)

end Yamabe3.Analysis.Delaunay
