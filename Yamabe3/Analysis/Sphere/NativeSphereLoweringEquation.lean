import Yamabe3.Analysis.Sphere.NativeSphereBochner

/-!
# Native spectral lowering on the round two-sphere

The previously constructed first-order lowering functions satisfy their
claimed equation for the actual scalar Laplacian.  The eigenvalue shift
is derived by the mixed Bochner identity, the true height Hessian and the
native Laplacian product rule.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SphereSpectrum

open Poincare.Geometry.Riemannian.SpaceForm

theorem sum_hessian_mul_height {n : ℕ} (D : LeviCivitaData (roundSphereMetric n))
    (f : UnitSphere n → ℝ) (a : Ambient n) (x : UnitSphere n) :
    (∑ i, ∑ j, D.hessian f x
      ((roundSphereMetric n).orthonormalBasis x i)
      ((roundSphereMetric n).orthonormalBasis x j) *
      D.hessian (height a) x ((roundSphereMetric n).orthonormalBasis x i)
        ((roundSphereMetric n).orthonormalBasis x j)) =
      -height a x * D.laplacian f x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : UnitSphere n → Type _) :=
    ⟨(roundSphereMetric n).toRiemannianMetric⟩
  let b := (roundSphereMetric n).orthonormalBasis x
  have hb (i j) : (roundSphereMetric n).inner x (b i) (b j) = if i = j then 1 else 0 := by
    exact b.inner_eq_ite i j
  have hrow (i) : (∑ j, D.hessian f x (b i) (b j) * D.hessian (height a) x (b i) (b j)) =
      -height a x * D.hessian f x (b i) (b i) := by
    simp_rw [hessian_height, hb]
    simp [mul_ite, mul_comm]
  change (∑ i, ∑ j, D.hessian f x (b i) (b j) * D.hessian (height a) x (b i) (b j)) = _
  simp_rw [hrow]
  rw [← Finset.mul_sum]
  rfl

theorem laplacian_inner_gradient_height (D : LeviCivitaData (roundSphereMetric 2))
    {f : UnitSphere 2 → ℝ} {μ : ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (heigen : ∀ x, -D.laplacian f x = μ * f x)
    (a : Ambient 2) (x : UnitSphere 2) :
    D.laplacian (fun y => (roundSphereMetric 2).inner y
      (D.gradient f y) (D.gradient (height a) y)) x =
      -μ * (roundSphereMetric 2).inner x (D.gradient f x) (D.gradient (height a) x) +
        2 * μ * height a x * f x := by
  have hLf : D.laplacian f = fun y => -μ * f y := by
    funext y
    linarith [heigen y]
  have hLh : D.laplacian (height a) = fun y => (-2 : ℝ) * height a y := by
    funext y
    simpa using laplacian_height D a y
  rw [mixed_bochner_roundTwoSphere D hf (smooth_height a), sum_hessian_mul_height,
    hLf, hLh, mvfderiv_const_mul, mvfderiv_const_mul,
    ← D.inner_gradient, ← D.inner_gradient,
    (roundSphereMetric 2).symm x (D.gradient (height a) x) (D.gradient f x)]
  ring

theorem lowering_eigen_equation (D : LeviCivitaData (roundSphereMetric 2))
    {f : UnitSphere 2 → ℝ} {α : ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (heigen : ∀ x, -D.laplacian f x = α * (α + 1) * f x)
    (a : Ambient 2) (x : UnitSphere 2) :
    -D.laplacian (lowering D f α a) x = α * (α - 1) * lowering D f α a x := by
  have hA := smooth_inner_gradients D hf (smooth_height a)
  have hterm : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun y => α * height a y * f y) :=
    (contMDiff_const.mul (smooth_height a)).mul hf
  have hfun : (fun y : UnitSphere 2 => α * height a y * f y) =
      fun y => α * (height a y * f y) := by funext y; ring
  have hL : D.laplacian f x = -(α * (α + 1)) * f x := by linarith [heigen x]
  unfold lowering
  rw [D.laplacian_add hA hterm, hfun, D.laplacian_const_mul,
    D.laplacian_mul (smooth_height a) hf,
    laplacian_inner_gradient_height D hf heigen a x,
    laplacian_height D a x, hL]
  rw [(roundSphereMetric 2).symm x (D.gradient (height a) x) (D.gradient f x)]
  norm_num
  ring

#print axioms laplacian_inner_gradient_height
#print axioms lowering_eigen_equation

end Yamabe3.Analysis.SphereSpectrum
