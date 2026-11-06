import Yamabe3.Analysis.NativeCanonicalCoefficients
import Yamabe3.Analysis.NativeFiniteLowProjection

/-! The actual future inverse of a continuous low source has C2 scalar
coefficients. No differentiability of the source is assumed. These are
coefficients of the original bounded linear inverse, not newly selected
solutions. The entrance values are retained, not set to zero. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.SphereSpectrum

theorem contDiff_two_of_continuous_second_deriv {u : ℝ → ℝ}
    (hu : Differentiable ℝ u) (hdu : Differentiable ℝ (deriv u))
    (hdd : Continuous (deriv (deriv u))) : ContDiff ℝ 2 u := by
  have h1 : ContDiff ℝ 1 (deriv u) :=
    contDiff_succ_iff_deriv.mpr ⟨hdu, by simp, contDiff_zero.mpr hdd⟩
  exact contDiff_succ_iff_deriv.mpr ⟨hu, by simp, h1⟩

theorem exponential_conjugate_second_deriv_C2 {u : ℝ → ℝ}
    (hu : Differentiable ℝ u) (hdu : Differentiable ℝ (deriv u)) (δ t : ℝ) :
    deriv (deriv (fun y => Real.exp (δ*y)*u y)) t =
      Real.exp (δ*t)*(δ^2*u t+2*δ*deriv u t+deriv (deriv u) t) := by
  have hexp (y : ℝ) : HasDerivAt (fun z : ℝ => Real.exp (δ*z))
      (δ*Real.exp (δ*y)) y := by
    apply (((hasDerivAt_id y).const_mul δ).exp).congr_deriv
    simp only [id_eq]
    ring
  have hfirst (y : ℝ) : HasDerivAt (fun z => Real.exp (δ*z)*u z)
      (Real.exp (δ*y)*(δ*u y+deriv u y)) y := by
    apply ((hexp y).mul (hu y).hasDerivAt).congr_deriv
    ring
  have hid : deriv (fun y => Real.exp (δ*y)*u y) =
      fun y => Real.exp (δ*y)*(δ*u y+deriv u y) := funext fun y => (hfirst y).deriv
  have h2 := (hexp t).mul ((((hu t).hasDerivAt).const_mul δ).add (hdu t).hasDerivAt)
  change HasDerivAt (fun y => Real.exp (δ*y)*(δ*u y+deriv u y))
    (δ*Real.exp (δ*t)*(δ*u t+deriv u t)+Real.exp (δ*t)*(δ*deriv u t+deriv (deriv u) t)) t at h2
  rw [hid, h2.deriv]
  ring

theorem nativeLowAngularInverseCLM_coefficient_C2 (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {k : ℝ} (hk : 0 < k) (hgap : 7/2 < k^2)
    (F : ℝ →ᵇ AngularL2)
    (hFhigh : ∀ i, 6 ≤ angularEigenvalue i → ∀ t, inner ℝ (angularBasis i) (F t) = 0)
    (i : AngularIndex) :
    ContDiff ℝ 2 (fun t => inner ℝ (angularBasis i)
      (nativeLowAngularInverseCLM v hv hb k hk hgap F t)) := by
  have he := nativeLowAngularInverseCLM_coordinate_equation v hv hb hk hgap F hFhigh i
  dsimp only at he
  apply contDiff_two_of_continuous_second_deriv he.1 he.2.1
  rw [show deriv (deriv (fun t => inner ℝ (angularBasis i)
      (nativeLowAngularInverseCLM v hv hb k hk hgap F t))) = _ from funext he.2.2]
  exact (((continuous_const.mul he.2.1.continuous).add
    (continuous_const.mul he.1.continuous)).add
    ((innerSL ℝ (angularBasis i)).continuous.comp F.continuous)).sub
    ((continuous_const.mul (hv.pow 4)).mul he.1.continuous)

theorem nativeLowAngularInverseCLM_weighted_coefficient_C2 (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {k : ℝ} (hk : 0 < k) (hgap : 7/2 < k^2)
    (F : ℝ →ᵇ AngularL2)
    (hFhigh : ∀ i, 6 ≤ angularEigenvalue i → ∀ t, inner ℝ (angularBasis i) (F t) = 0)
    (i : AngularIndex) :
    let u := fun t => Real.exp (-k*t)*inner ℝ (angularBasis i)
      (nativeLowAngularInverseCLM v hv hb k hk hgap F t)
    ContDiff ℝ 2 u ∧ ∀ t, modelJacobi v (angularEigenvalue i) u t =
      Real.exp (-k*t)*inner ℝ (angularBasis i) (F t) := by
  dsimp only
  have he := nativeLowAngularInverseCLM_coordinate_equation v hv hb hk hgap F hFhigh i
  dsimp only at he
  refine ⟨(Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul
    (nativeLowAngularInverseCLM_coefficient_C2 v hv hb hk hgap F hFhigh i), ?_⟩
  intro t
  unfold modelJacobi
  rw [exponential_conjugate_second_deriv_C2 he.1 he.2.1,he.2.2 t]
  ring

/-- The future inverse retains exactly the actual finite low space. -/
theorem nativeLowAngularInverseCLM_low (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {k : ℝ} (hk : 0 < k) (hgap : 7/2 < k^2)
    (F : ℝ →ᵇ AngularL2)
    (hFhigh : ∀ i, 6 ≤ angularEigenvalue i → ∀ t, inner ℝ (angularBasis i) (F t) = 0)
    (t : ℝ) : nativeLowProjection (nativeLowAngularInverseCLM v hv hb k hk hgap F t) =
      nativeLowAngularInverseCLM v hv hb k hk hgap F t := by
  classical
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply,nativeLowProjection,nativeAngularProjection_coefficient]
  split_ifs with hi
  · rfl
  · exact (nativeLowAngularInverseCLM_coordinate_zero v hv hb hk hgap F i
      (hFhigh i (le_of_not_gt hi)) t).symm

#print axioms contDiff_two_of_continuous_second_deriv
#print axioms exponential_conjugate_second_deriv_C2
#print axioms nativeLowAngularInverseCLM_coefficient_C2
#print axioms nativeLowAngularInverseCLM_weighted_coefficient_C2
#print axioms nativeLowAngularInverseCLM_low
end Yamabe3.Analysis.Delaunay
