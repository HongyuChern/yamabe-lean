import Yamabe3.Analysis.SpectralIntegralPotentialInverse
import Yamabe3.Analysis.NativeAngularInverse
import Yamabe3.Analysis.DelaunayWeightedInverse

/-!
# Native angular inverse with the genuine integrated potential criterion

The actual native Hilbert basis transports the aggregate Bochner fixed
point. Low coordinates of a true high-mode source remain zero by the
proved iteration invariant, even when the older sup-potential criterion
is unavailable. The small-neck application discharges the displayed
integrated criterion from actual period/mass data.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory PoincareMT
open scoped Topology lp ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.SphereSpectrum

def nativeIntegralAngularInverse {δ κ : ℝ} (hδ : |δ| < 5 / 2)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) δ s * |V (t - s)|) ≤ κ)
    (F : ℝ →ᵇ AngularL2) : ℝ →ᵇ AngularL2 :=
  let U := spectralIntegralPotentialInverse nativeAngularRate (by norm_num)
    nativeAngularRate_lower hδ hκ0 hκ1 V hV (angularSourceCoordinates F)
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => angularBasis.repr.symm (U t))
    (angularBasis.repr.symm.continuous.comp U.continuous) ‖U‖
    (fun t => by simpa only [LinearIsometryEquiv.norm_map] using U.norm_coe_le_norm t)

theorem nativeIntegralAngularInverse_coefficient {δ κ : ℝ} (hδ : |δ| < 5 / 2)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) δ s * |V (t - s)|) ≤ κ)
    (F : ℝ →ᵇ AngularL2) (t : ℝ) (i : AngularIndex) :
    inner ℝ (angularBasis i) (nativeIntegralAngularInverse hδ hκ0 hκ1 V hV F t) =
      spectralIntegralPotentialInverse nativeAngularRate (by norm_num)
        nativeAngularRate_lower hδ hκ0 hκ1 V hV (angularSourceCoordinates F) t i := by
  rw [← HilbertBasis.repr_apply_apply]
  change angularBasis.repr (angularBasis.repr.symm _) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem nativeIntegralAngularInverse_norm_le {δ κ : ℝ} (hδ : |δ| < 5 / 2)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) δ s * |V (t - s)|) ≤ κ)
    (F : ℝ →ᵇ AngularL2) :
    ‖nativeIntegralAngularInverse hδ hκ0 hκ1 V hV F‖ ≤
      (‖F‖ / ((5 / 2 : ℝ) ^ 2 - δ ^ 2)) / (1 - κ) := by
  let U := spectralIntegralPotentialInverse nativeAngularRate (by norm_num)
    nativeAngularRate_lower hδ hκ0 hκ1 V hV (angularSourceCoordinates F)
  have hn : ‖nativeIntegralAngularInverse hδ hκ0 hκ1 V hV F‖ ≤ ‖U‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg U)).mpr
    intro t
    change ‖angularBasis.repr.symm (U t)‖ ≤ ‖U‖
    simpa only [LinearIsometryEquiv.norm_map] using U.norm_coe_le_norm t
  have hgap : 0 < (5 / 2 : ℝ) ^ 2 - δ ^ 2 := by
    have h := abs_lt.mp hδ
    have hm := mul_pos (sub_pos.mpr h.2) (show 0 < (5 / 2 : ℝ) + δ by linarith [h.1])
    nlinarith only [hm]
  calc
    _ ≤ ‖U‖ := hn
    _ ≤ (‖angularSourceCoordinates F‖ / ((5 / 2 : ℝ) ^ 2 - δ ^ 2)) / (1 - κ) :=
      spectralIntegralPotentialInverse_norm_le nativeAngularRate (by norm_num)
        nativeAngularRate_lower hδ hκ0 hκ1 V hV (angularSourceCoordinates F)
    _ ≤ _ := div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right (angularSourceCoordinates_norm_le F) hgap.le)
      (sub_pos.mpr hκ1).le

theorem nativeIntegralAngularInverse_coordinate_zero {δ κ : ℝ} (hδ : |δ| < 5 / 2)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) δ s * |V (t - s)|) ≤ κ)
    (F : ℝ →ᵇ AngularL2) (i : AngularIndex)
    (hF : ∀ t, inner ℝ (angularBasis i) (F t) = 0) :
    ∀ t, inner ℝ (angularBasis i) (nativeIntegralAngularInverse hδ hκ0 hκ1 V hV F t) = 0 := by
  intro t
  rw [nativeIntegralAngularInverse_coefficient]
  apply spectralIntegralPotentialInverse_coordinate_zero nativeAngularRate (by norm_num)
    nativeAngularRate_lower hδ hκ0 hκ1 V hV (angularSourceCoordinates F) i
    (fun s => by rw [angularSourceCoordinates_apply, hF]) t

theorem nativeIntegralAngularInverse_coordinate_equation {δ κ : ℝ} (hδ : |δ| < 5 / 2)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) δ s * |V (t - s)|) ≤ κ)
    (F : ℝ →ᵇ AngularL2)
    (hFlow : ∀ i, angularEigenvalue i < 6 → ∀ t, inner ℝ (angularBasis i) (F t) = 0)
    (i : AngularIndex) :
    let u := fun t => inner ℝ (angularBasis i) (nativeIntegralAngularInverse hδ hκ0 hκ1 V hV F t)
    Differentiable ℝ u ∧ Differentiable ℝ (deriv u) ∧
      ∀ t, deriv (deriv u) t = -2 * δ * deriv u t +
        (angularEigenvalue i + 1 / 4 - δ ^ 2) * u t +
          inner ℝ (angularBasis i) (F t) - V t * u t := by
  dsimp only
  have hrep : (fun t => inner ℝ (angularBasis i)
      (nativeIntegralAngularInverse hδ hκ0 hκ1 V hV F t)) =
      fun t => spectralIntegralPotentialInverse nativeAngularRate (by norm_num)
        nativeAngularRate_lower hδ hκ0 hκ1 V hV (angularSourceCoordinates F) t i :=
    funext fun t => nativeIntegralAngularInverse_coefficient hδ hκ0 hκ1 V hV F t i
  have h := spectralIntegralPotentialInverse_coordinate_equation nativeAngularRate (by norm_num)
    nativeAngularRate_lower hδ hκ0 hκ1 V hV (angularSourceCoordinates F) i
  dsimp only at h
  rw [← hrep] at h
  refine ⟨h.1, h.2.1, fun t => ?_⟩
  have he := h.2.2 t
  rw [nativeAngularRate_sq, angularSourceCoordinates_apply, ← congrFun hrep t] at he
  by_cases hi : 6 ≤ angularEigenvalue i
  · simpa only [max_eq_right hi] using he
  · have hz := nativeIntegralAngularInverse_coordinate_zero hδ hκ0 hκ1 V hV F i
      (hFlow i (lt_of_not_ge hi)) t
    simpa only [hz, mul_zero] using he

/-- The integrated potential criterion gives the same genuine native
weighted solution and exact equation in every actual angular coefficient.
The potential remains the actual common Delaunay function 15*v^4/4. -/
theorem exists_native_integral_angular_weighted_solution {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1)
    {δ κ : ℝ} (hδ : |δ| < 5 / 2) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) δ s * ((15 / 4) * v (t - s) ^ 4)) ≤ κ)
    (F : ℝ →ᵇ AngularL2)
    (hFs : ∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (F t)))
    (hFlow : ∀ i, angularEigenvalue i < 6 → ∀ t, inner ℝ (angularBasis i) (F t) = 0) :
    ∃ U : ℝ → AngularL2, Continuous U ∧
      (∀ t, ‖U t‖ ≤ ((‖F‖ / ((5 / 2 : ℝ) ^ 2 - δ ^ 2)) / (1 - κ)) * Real.exp (δ * t)) ∧
      (∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (U t)) ∧
        ∀ t, modelJacobi v (angularEigenvalue i) (fun s => inner ℝ (angularBasis i) (U s)) t =
          Real.exp (δ * t) * inner ℝ (angularBasis i) (F t)) ∧
      (∀ i, angularEigenvalue i < 6 → ∀ t, inner ℝ (angularBasis i) (U t) = 0) ∧
      (∀ t, HasSum (fun i => inner ℝ (angularBasis i) (U t) • angularBasis i) (U t)) := by
  let Vf : ℝ → ℝ := fun t => (15 / 4) * v t ^ 4
  have hVs : ContDiff ℝ ∞ Vf := contDiff_const.mul (hv.pow 4)
  have hVb (t : ℝ) : ‖Vf t‖ ≤ 15 / 4 := by
    have hpow : v t ^ 4 ≤ 1 := pow_le_one₀ (hb t).1 (hb t).2
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [Vf]; positivity)]
    dsimp [Vf]
    linarith
  let V : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup Vf hVs.continuous (15 / 4) hVb
  have hVi : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) δ s * |V (t - s)|) ≤ κ := by
    intro t
    convert hV t using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun s => by
      change spectralMajorant (5 / 2) δ s * |(15 / 4) * v (t - s) ^ 4| = _
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (15 / 4) * v (t - s) ^ 4)]
  let w := nativeIntegralAngularInverse hδ hκ0 hκ1 V hVi F
  let U : ℝ → AngularL2 := fun t => Real.exp (δ * t) • w t
  have hwn := nativeIntegralAngularInverse_norm_le hδ hκ0 hκ1 V hVi F
  have hcoef (i : AngularIndex) (t : ℝ) :
      inner ℝ (angularBasis i) (U t) = Real.exp (δ * t) * inner ℝ (angularBasis i) (w t) := by
    dsimp [U]
    rw [real_inner_smul_right]
  refine ⟨U, (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul w.continuous,
    ?_, ?_, ?_, fun t => angularBasis_reconstruct (U t)⟩
  · intro t
    dsimp [U]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (δ * t) * ((‖F‖ / ((5 / 2 : ℝ) ^ 2 - δ ^ 2)) / (1 - κ)) :=
        mul_le_mul_of_nonneg_left ((w.norm_coe_le_norm t).trans hwn) (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  · intro i
    have heq := nativeIntegralAngularInverse_coordinate_equation hδ hκ0 hκ1 V hVi F hFlow i
    dsimp only at heq
    have hws : ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (w t)) :=
      contDiff_of_second_order_linear_drift heq.1 heq.2.1 hVs (hFs i) heq.2.2
    have hefun : (fun t => inner ℝ (angularBasis i) (U t)) =
        fun t => Real.exp (δ * t) * inner ℝ (angularBasis i) (w t) := funext (hcoef i)
    rw [hefun]
    refine ⟨(Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul hws, fun t => ?_⟩
    have hODE := heq.2.2 t
    change deriv (deriv (fun s => inner ℝ (angularBasis i) (w s))) t =
      -2 * δ * deriv (fun s => inner ℝ (angularBasis i) (w s)) t +
        (angularEigenvalue i + 1 / 4 - δ ^ 2) * inner ℝ (angularBasis i) (w t) +
          inner ℝ (angularBasis i) (F t) - (15 / 4) * v t ^ 4 * inner ℝ (angularBasis i) (w t) at hODE
    unfold modelJacobi
    rw [exponential_conjugate_second_deriv hws, hODE]
    ring
  · intro i hi t
    rw [hcoef, nativeIntegralAngularInverse_coordinate_zero hδ hκ0 hκ1 V hVi F i
      (hFlow i hi) t, mul_zero]

end Yamabe3.Analysis.Delaunay
