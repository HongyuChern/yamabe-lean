import Yamabe3.Analysis.Cylinder.NativeSphereRestriction
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Native Euclidean Laplacian in genuine polar variables

Dilation and the proved restriction formula give the true Euclidean
Laplacian in terms of the actual induced sphere Laplacian.  Radial first
and second derivatives are proved by ordinary Frechet/one-variable chain
rules; the polar expression is a theorem about the native operator.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

open Set Filter PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open Poincare.Geometry.Riemannian.SpaceForm

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem fderiv2_comp_smul (f : E → ℝ) (r : ℝ) (x u v : E) :
    fderiv ℝ (fderiv ℝ (fun y => f (r • y))) x u v =
      r ^ 2 * fderiv ℝ (fderiv ℝ f) (r • x) u v := by
  have h : fderiv ℝ (fun y => f (r • y)) = fun y => r • fderiv ℝ f (r • y) := by
    funext y
    exact fderiv_comp_smul r
  rw [h]
  have hs : fderiv ℝ (fun y : E => r • fderiv ℝ f (r • y)) x =
      r • fderiv ℝ (fun y : E => fderiv ℝ f (r • y)) x := by
    simpa only [Pi.smul_def] using congrFun
      (fderiv_const_smul_field (𝕜 := ℝ) (f := fun y : E => fderiv ℝ f (r • y)) r) x
  rw [hs, fderiv_comp_smul]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem laplacian_comp_smul {f : E → ℝ} (r : ℝ) {x : E}
    (hf : ContDiffAt ℝ ∞ f (r • x)) :
    euclideanD.laplacian (fun y => f (r • y)) x =
      r ^ 2 * euclideanD.laplacian f (r • x) := by
  have hg : ContDiffAt ℝ ∞ (fun y => f (r • y)) x :=
    hf.comp x (contDiffAt_id.const_smul r)
  rw [euclideanD.laplacian_euclideanMetric hg, euclideanD.laplacian_euclideanMetric hf]
  simp only [fderiv2_comp_smul, Finset.mul_sum]

theorem laplacian_dilated_restriction {f : E → ℝ} (r : ℝ) (x : S)
    (hf : ContDiffAt ℝ ∞ f (r • (x : E))) :
    sphereD.laplacian (fun y : S => f (r • (y : E))) x =
      r ^ 2 * (euclideanD.laplacian f (r • (x : E)) -
        fderiv ℝ (fderiv ℝ f) (r • (x : E)) (x : E) (x : E)) -
      2 * r * fderiv ℝ f (r • (x : E)) (x : E) := by
  have hg : ContDiffAt ℝ ∞ (fun y : E => f (r • y)) (x : E) :=
    hf.comp (x : E) (contDiffAt_id.const_smul r)
  have h := laplacian_restriction (f := fun y => f (r • y)) x hg
  rw [laplacian_comp_smul r hf, fderiv2_comp_smul, fderiv_comp_smul] at h
  simp only [smul_apply, smul_eq_mul] at h
  convert h using 1 <;> ring

theorem laplacian_polar_frechet {f : E → ℝ} {r : ℝ} (hr : 0 < r) (x : S)
    (hf : ContDiffAt ℝ ∞ f (r • (x : E))) :
    euclideanD.laplacian f (r • (x : E)) =
      fderiv ℝ (fderiv ℝ f) (r • (x : E)) (x : E) (x : E) +
      2 / r * fderiv ℝ f (r • (x : E)) (x : E) +
      r⁻¹ ^ 2 * sphereD.laplacian (fun y : S => f (r • (y : E))) x := by
  have h := laplacian_dilated_restriction r x hf
  rw [h]
  field_simp [hr.ne']
  ring

theorem deriv_radial_slice {f : E → ℝ} {r : ℝ} (x : E)
    (hf : DifferentiableAt ℝ f (r • x)) :
    deriv (fun s : ℝ => f (s • x)) r = fderiv ℝ f (r • x) x := by
  simpa only [one_smul, Function.comp_def, id_eq] using
    (hf.hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_id r).smul_const x)).deriv

theorem second_deriv_radial_slice {f : E → ℝ} {r : ℝ} (x : E)
    (hf : ContDiffAt ℝ ∞ f (r • x)) :
    deriv (deriv (fun s : ℝ => f (s • x))) r =
      fderiv ℝ (fderiv ℝ f) (r • x) x x := by
  have hn : ∀ᶠ y in 𝓝 (r • x), DifferentiableAt ℝ f y := by
    filter_upwards [(hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)] with y hy
    exact hy.differentiableAt (by simp)
  have hc : ContinuousAt (fun s : ℝ => s • x) r :=
    continuousAt_id.smul continuousAt_const
  have heq : deriv (fun s : ℝ => f (s • x)) =ᶠ[𝓝 r]
      fun s => fderiv ℝ f (s • x) x := by
    filter_upwards [hc.eventually hn] with s hs
    exact deriv_radial_slice x hs
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) (r • x) :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hcurve := hdf.hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_id r).smul_const x)
  have hd : HasDerivAt (fun s => fderiv ℝ f (s • x) x)
      (fderiv ℝ (fderiv ℝ f) (r • x) x x) r := by
    simpa using hcurve.clm_apply (hasDerivAt_const r x)
  exact (hd.congr_of_eventuallyEq heq).deriv

theorem laplacian_polar {f : E → ℝ} {r : ℝ} (hr : 0 < r) (x : S)
    (hf : ContDiffAt ℝ ∞ f (r • (x : E))) :
    euclideanD.laplacian f (r • (x : E)) =
      deriv (deriv (fun s : ℝ => f (s • (x : E)))) r +
      2 / r * deriv (fun s : ℝ => f (s • (x : E))) r +
      r⁻¹ ^ 2 * sphereD.laplacian (fun y : S => f (r • (y : E))) x := by
  rw [second_deriv_radial_slice (x : E) hf,
    deriv_radial_slice (x : E) (hf.differentiableAt (by simp))]
  exact laplacian_polar_frechet hr x hf

#print axioms laplacian_dilated_restriction
#print axioms laplacian_polar

end Yamabe3.Analysis.SpherePolar
