import Yamabe3.Analysis.NativeAngularInverseLinearity
import Yamabe3.Analysis.BanachFutureObservable

/-!
# Actual equations for the canonical native inverse curves

These statements concern the explicit continuous linear operators, not
witnesses chosen from an existence theorem. Consequently the smooth scalar
realization constructed later retains exactly the curve on which source
linearity and difference estimates hold.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory PoincareMT
open scoped Topology lp ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.SphereSpectrum

theorem nativeLowAngularInverseCLM_coordinate_zero (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {k : ℝ} (hk : 0 < k) (hgap : 7 / 2 < k ^ 2)
    (F : ℝ →ᵇ AngularL2) (i : AngularIndex)
    (hF : ∀ t, inner ℝ (angularBasis i) (F t) = 0) :
    ∀ t, inner ℝ (angularBasis i) (nativeLowAngularInverseCLM v hv hb k hk hgap F t) = 0 := by
  let A := lowAngularOperatorBCF v hv hb
  let L := lp.evalCLM ℝ (fun _ : AngularIndex => ℝ) 2 i
  intro t
  rw [nativeLowAngularInverseCLM_apply, ← HilbertBasis.repr_apply_apply,
    LinearIsometryEquiv.apply_symm_apply]
  apply banachFuturePotentialInverse_observable_zero hk A
    ((lowAngularOperatorBCF_norm_le v hv hb).trans_lt hgap) (angularSourceCoordinates F) L
    (fun s => by change angularSourceCoordinates F s i = 0; rw [angularSourceCoordinates_apply, hF])
    (fun s x hx => ?_) t
  change lowAngularCoefficient v s i * x i = 0
  change x i = 0 at hx
  rw [hx, mul_zero]

theorem nativeLowAngularInverseCLM_coordinate_equation (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {k : ℝ} (hk : 0 < k) (hgap : 7 / 2 < k ^ 2)
    (F : ℝ →ᵇ AngularL2)
    (hFhigh : ∀ i, 6 ≤ angularEigenvalue i → ∀ t, inner ℝ (angularBasis i) (F t) = 0)
    (i : AngularIndex) :
    let u := fun t => inner ℝ (angularBasis i) (nativeLowAngularInverseCLM v hv hb k hk hgap F t)
    Differentiable ℝ u ∧ Differentiable ℝ (deriv u) ∧
      ∀ t, deriv (deriv u) t = 2 * k * deriv u t +
        (angularEigenvalue i + 1 / 4 - k ^ 2) * u t +
        inner ℝ (angularBasis i) (F t) - (15 / 4) * v t ^ 4 * u t := by
  dsimp only
  let A := lowAngularOperatorBCF v hv hb
  have hAg : ‖A‖ < k ^ 2 := (lowAngularOperatorBCF_norm_le v hv hb).trans_lt hgap
  let Fc := angularSourceCoordinates F
  let w := banachFuturePotentialInverse k hk A hAg Fc
  let L := lp.evalCLM ℝ (fun _ : AngularIndex => ℝ) 2 i
  have hrep : (fun t => inner ℝ (angularBasis i)
      (nativeLowAngularInverseCLM v hv hb k hk hgap F t)) = fun t => L (w t) := by
    funext t
    rw [nativeLowAngularInverseCLM_apply, ← HilbertBasis.repr_apply_apply,
      LinearIsometryEquiv.apply_symm_apply]
    rfl
  have heq := banachFuturePotentialInverse_observable_equation hk A hAg Fc L
    (fun t => lowAngularCoefficient v t i) (fun _ _ => rfl)
  dsimp only at heq
  rw [hrep]
  refine ⟨heq.1, heq.2.1, fun t => ?_⟩
  have hODE := heq.2.2 t
  change deriv (deriv (fun s => L (w s))) t = 2 * k * deriv (fun s => L (w s)) t -
    k ^ 2 * L (w t) + Fc t i + lowAngularCoefficient v t i * L (w t) at hODE
  rw [angularSourceCoordinates_apply] at hODE
  have hcprod : lowAngularCoefficient v t i * L (w t) =
      (1 / 4 + angularEigenvalue i - (15 / 4) * v t ^ 4) * L (w t) := by
    by_cases hi : angularEigenvalue i < 6
    · rw [lowAngularCoefficient, if_pos hi]
    · have hz := nativeLowAngularInverseCLM_coordinate_zero v hv hb hk hgap F i
        (hFhigh i (le_of_not_gt hi)) t
      rw [congrFun hrep t] at hz
      rw [hz, mul_zero, mul_zero]
  rw [hcprod] at hODE
  rw [congrFun hrep t]
  nlinarith only [hODE]

/-- Smooth coefficients and the genuine native ODE for the exact low CLM. -/
theorem nativeLowAngularInverseCLM_weighted_coefficient {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1)
    {k : ℝ} (hk : 0 < k) (hgap : 7 / 2 < k ^ 2)
    (F : ℝ →ᵇ AngularL2)
    (hFs : ∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (F t)))
    (hFhigh : ∀ i, 6 ≤ angularEigenvalue i → ∀ t, inner ℝ (angularBasis i) (F t) = 0)
    (i : AngularIndex) :
    let u := fun t => Real.exp (-k * t) *
      inner ℝ (angularBasis i) (nativeLowAngularInverseCLM v hv.continuous hb k hk hgap F t)
    ContDiff ℝ ∞ u ∧ ∀ t, modelJacobi v (angularEigenvalue i) u t =
      Real.exp (-k * t) * inner ℝ (angularBasis i) (F t) := by
  dsimp only
  let w := fun t => inner ℝ (angularBasis i)
    (nativeLowAngularInverseCLM v hv.continuous hb k hk hgap F t)
  have heq := nativeLowAngularInverseCLM_coordinate_equation v hv.continuous hb hk hgap F hFhigh i
  dsimp only at heq
  have hVs : ContDiff ℝ ∞ (fun t => (15 / 4 : ℝ) * v t ^ 4) := contDiff_const.mul (hv.pow 4)
  have hws : ContDiff ℝ ∞ w :=
    contDiff_of_second_order_linear_drift heq.1 heq.2.1 hVs (hFs i) heq.2.2
  refine ⟨(Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul hws, fun t => ?_⟩
  unfold modelJacobi
  rw [exponential_conjugate_second_deriv hws, heq.2.2 t]
  ring

/-- Smooth coefficients and the genuine native ODE for the exact high CLM. -/
theorem nativeIntegralAngularInverseCLM_weighted_coefficient {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) {δ κ : ℝ} (hδ : |δ| < 5 / 2)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) δ s * |V (t - s)|) ≤ κ)
    (hVval : ∀ t, V t = (15 / 4) * v t ^ 4)
    (F : ℝ →ᵇ AngularL2)
    (hFs : ∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (F t)))
    (hFlow : ∀ i, angularEigenvalue i < 6 → ∀ t, inner ℝ (angularBasis i) (F t) = 0)
    (i : AngularIndex) :
    let u := fun t => Real.exp (δ * t) *
      inner ℝ (angularBasis i) (nativeIntegralAngularInverseCLM hδ hκ0 hκ1 V hV F t)
    ContDiff ℝ ∞ u ∧ ∀ t, modelJacobi v (angularEigenvalue i) u t =
      Real.exp (δ * t) * inner ℝ (angularBasis i) (F t) := by
  dsimp only
  rw [nativeIntegralAngularInverseCLM_apply]
  let w := fun t => inner ℝ (angularBasis i) (nativeIntegralAngularInverse hδ hκ0 hκ1 V hV F t)
  have heq := nativeIntegralAngularInverse_coordinate_equation hδ hκ0 hκ1 V hV F hFlow i
  dsimp only at heq
  have hVs : ContDiff ℝ ∞ (fun t => V t) := by
    have he : (fun t => V t) = fun t => (15 / 4 : ℝ) * v t ^ 4 := funext hVval
    rw [he]
    exact contDiff_const.mul (hv.pow 4)
  have hws : ContDiff ℝ ∞ w :=
    contDiff_of_second_order_linear_drift heq.1 heq.2.1 hVs (hFs i) heq.2.2
  refine ⟨(Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul hws, fun t => ?_⟩
  unfold modelJacobi
  rw [exponential_conjugate_second_deriv hws, heq.2.2 t, hVval]
  ring

end Yamabe3.Analysis.Delaunay
