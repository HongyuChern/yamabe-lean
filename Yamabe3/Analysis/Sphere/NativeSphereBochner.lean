import Yamabe3.Analysis.Sphere.NativeSphereLowering
import PoincareLib.Geometry.Riemannian.SpaceForm.SphereCurvature
import PoincareLib.Geometry.Riemannian.ScalarOperators.Bochner
import PoincareLib.Geometry.Riemannian.ScalarOperators.Linearity
import PoincareLib.Geometry.Riemannian.ScalarOperators.Product
import PoincareLib.Geometry.Riemannian.ScalarOperators.Divergence.Regularity

/-!
# Mixed Bochner identity for the actual round two-sphere

The Ricci tensor is contracted from the actual induced curvature tensor.
Polarization of the native Bochner identity then gives the differential
identity needed for lowering true angular eigenfunctions.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

open Set Filter PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SphereSpectrum

open Poincare.Geometry.Riemannian.SpaceForm

theorem roundSphere_ricci {n : ℕ} (D : LeviCivitaData (roundSphereMetric n))
    (x : UnitSphere n) (u v : TangentSpace (𝓡 n) x) :
    D.ricci x u v = ((n : ℝ) - 1) * (roundSphereMetric n).inner x u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : UnitSphere n → Type _) :=
    ⟨(roundSphereMetric n).toRiemannianMetric⟩
  have hunit (i) : (roundSphereMetric n).inner x
      ((roundSphereMetric n).orthonormalBasis x i)
      ((roundSphereMetric n).orthonormalBasis x i) = 1 := by
    change inner ℝ ((roundSphereMetric n).orthonormalBasis x i)
      ((roundSphereMetric n).orthonormalBasis x i) = 1
    simp
  have hsum := ((roundSphereMetric n).orthonormalBasis x).sum_inner_mul_inner u v
  change (∑ i, (roundSphereMetric n).inner x u ((roundSphereMetric n).orthonormalBasis x i) *
    (roundSphereMetric n).inner x ((roundSphereMetric n).orthonormalBasis x i) v) =
      (roundSphereMetric n).inner x u v at hsum
  unfold LeviCivitaData.ricci
  simp_rw [roundSphereMetric_curvatureTensor, hunit, mul_one]
  rw [Finset.sum_sub_distrib, hsum]
  simp [TangentSpace]
  ring

theorem bochner_roundTwoSphere (D : LeviCivitaData (roundSphereMetric 2))
    {f : UnitSphere 2 → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (x : UnitSphere 2) :
    D.laplacian (fun y => (roundSphereMetric 2).inner y (D.gradient f y) (D.gradient f y)) x =
      2 * (∑ i, ∑ j, (D.hessian f x
        ((roundSphereMetric 2).orthonormalBasis x i)
        ((roundSphereMetric 2).orthonormalBasis x j)) ^ 2) +
      2 * mvfderiv (𝓡 2) (D.laplacian f) x (D.gradient f x) +
      2 * (roundSphereMetric 2).inner x (D.gradient f x) (D.gradient f x) := by
  simpa only [roundSphere_ricci, Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num,
    one_mul] using D.bochner_identity hf x

theorem mixed_bochner_roundTwoSphere (D : LeviCivitaData (roundSphereMetric 2))
    {f h : UnitSphere 2 → ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h) (x : UnitSphere 2) :
    D.laplacian (fun y => (roundSphereMetric 2).inner y (D.gradient f y) (D.gradient h y)) x =
      2 * (∑ i, ∑ j, D.hessian f x
        ((roundSphereMetric 2).orthonormalBasis x i)
        ((roundSphereMetric 2).orthonormalBasis x j) *
          D.hessian h x ((roundSphereMetric 2).orthonormalBasis x i)
            ((roundSphereMetric 2).orthonormalBasis x j)) +
      mvfderiv (𝓡 2) (D.laplacian f) x (D.gradient h x) +
      mvfderiv (𝓡 2) (D.laplacian h) x (D.gradient f x) +
      2 * (roundSphereMetric 2).inner x (D.gradient f x) (D.gradient h x) := by
  let g := roundSphereMetric 2
  let Qf := fun y => g.inner y (D.gradient f y) (D.gradient f y)
  let Qh := fun y => g.inner y (D.gradient h y) (D.gradient h y)
  let A := fun y => g.inner y (D.gradient f y) (D.gradient h y)
  have hQf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ Qf := smooth_inner_gradients D hf hf
  have hQh : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ Qh := smooth_inner_gradients D hh hh
  have hA : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ A := smooth_inner_gradients D hf hh
  have hnorm : (fun y => g.inner y (D.gradient (fun z => f z + h z) y)
      (D.gradient (fun z => f z + h z) y)) = fun y => (Qf y + Qh y) + 2 * A y := by
    funext y
    rw [D.gradient_add ((hf y).mdifferentiableAt (by simp))
      ((hh y).mdifferentiableAt (by simp))]
    simp only [map_add, add_apply, Qf, Qh, A]
    rw [g.symm y (D.gradient h y) (D.gradient f y)]
    ring
  have hL : D.laplacian (fun y => f y + h y) =
      fun y => D.laplacian f y + D.laplacian h y := by
    funext y
    exact D.laplacian_add hf hh y
  have hdf := ((D.contMDiff_laplacian hf) x).mdifferentiableAt (by simp)
  have hdh := ((D.contMDiff_laplacian hh) x).mdifferentiableAt (by simp)
  have hG := D.gradient_add ((hf x).mdifferentiableAt (by simp))
    ((hh x).mdifferentiableAt (by simp))
  let b := g.orthonormalBasis x
  have hH : (∑ i, ∑ j, (D.hessian (fun y => f y + h y) x (b i) (b j)) ^ 2) =
      (∑ i, ∑ j, (D.hessian f x (b i) (b j)) ^ 2) +
      2 * (∑ i, ∑ j, D.hessian f x (b i) (b j) * D.hessian h x (b i) (b j)) +
      (∑ i, ∑ j, (D.hessian h x (b i) (b j)) ^ 2) := by
    simp_rw [D.hessian_add hf hh, add_sq]
    simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  have hsum := bochner_roundTwoSphere D (hf.add hh) x
  have hfirst := bochner_roundTwoSphere D hf x
  have hsecond := bochner_roundTwoSphere D hh x
  have h2A : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun y => (2 : ℝ) * A y) :=
    contMDiff_const.mul hA
  have hAdd : D.laplacian (fun y => (Qf y + Qh y) + 2 * A y) x =
      D.laplacian (fun y => Qf y + Qh y) x +
        D.laplacian (fun y => 2 * A y) x := by
    simpa only [Pi.add_def] using D.laplacian_add (hQf.add hQh) h2A x
  have hAddLeft : D.laplacian (fun y => (Qf y + Qh y) + 2 * A y) x =
      D.laplacian Qf x + D.laplacian Qh x + 2 * D.laplacian A x := by
    rw [hAdd, D.laplacian_add hQf hQh, D.laplacian_const_mul]
  change D.laplacian (fun y => g.inner y (D.gradient (fun z => f z + h z) y)
    (D.gradient (fun z => f z + h z) y)) x =
    2 * (∑ i, ∑ j, (D.hessian (fun y => f y + h y) x (b i) (b j)) ^ 2) +
      2 * mvfderiv (𝓡 2) (D.laplacian (fun y => f y + h y)) x
        (D.gradient (fun y => f y + h y) x) +
      2 * g.inner x (D.gradient (fun y => f y + h y) x)
        (D.gradient (fun y => f y + h y) x) at hsum
  rw [hnorm, hAddLeft, hH, hL, mvfderiv_fun_add hdf hdh, hG] at hsum
  simp only [map_add, add_apply] at hsum
  rw [g.symm x (D.gradient h x) (D.gradient f x)] at hsum
  change D.laplacian Qf x = _ at hfirst
  change D.laplacian Qh x = _ at hsecond
  change D.laplacian A x = _
  dsimp only [Qf, Qh, A, b, g] at hsum hfirst hsecond ⊢
  linarith only [hsum, hfirst, hsecond]

#print axioms roundSphere_ricci
#print axioms mixed_bochner_roundTwoSphere

end Yamabe3.Analysis.SphereSpectrum
