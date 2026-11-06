import Yamabe3.Analysis.Green.NativeLocalParametrix
import PoincareLib.Geometry.Riemannian.ScalarOperators.Composition

/-!
# The actual native Newton operator away from its pole

Gauss's identity determines the actual gradient. The native density
divergence formula then computes the Laplacian of 1/r at every nonzero point.
This is a pointwise statement for the actual metric and complements the
already proved distributional point-source identity.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT Yamabe3.RegularizedNewton

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem native_gradient_inv_norm (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E, g.inner x x v = inner ℝ x v)
    {x : E} (hx : x ≠ 0) :
    g.leviCivitaData.gradient (fun y : E => ‖y‖⁻¹) x = -(‖x‖ ^ 3)⁻¹ • x := by
  let D := g.leviCivitaData
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hnorm : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y : E => ‖y‖) x :=
    (contDiffAt_norm ℝ hx (n := ∞)).contMDiffAt
  have hgrad : D.gradient (fun y : E => ‖y‖) x = ‖x‖⁻¹ • x := by
    have h := D.gradient_radial_coordinate (OpenPartialHomeomorph.refl E)
      contMDiffOn_id contMDiffOn_id (mem_univ x) hx
      (by intro v; convert! hGauss x v using 1; simp; rfl)
    convert! h using 1
    simp
    rfl
  have hcomp : D.gradient (fun y : E => ‖y‖⁻¹) x =
      -(‖x‖ ^ 2)⁻¹ • D.gradient (fun y : E => ‖y‖) x := by
    simpa only [Function.comp_def, deriv_inv] using
      D.gradient_comp (hnorm.mdifferentiableAt (by simp)) (differentiableAt_inv hn)
  calc
    _ = -(‖x‖ ^ 2)⁻¹ • D.gradient (fun y : E => ‖y‖) x := hcomp
    _ = -(‖x‖ ^ 2)⁻¹ • (‖x‖⁻¹ • x) := by rw [hgrad]
    _ = _ := by
      rw [smul_smul]
      congr 1
      field_simp

theorem native_negative_laplacian_inv_norm (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E, g.inner x x v = inner ℝ x v)
    {x : E} (hx : x ≠ 0) :
    -g.leviCivitaData.laplacian (fun y : E => ‖y‖⁻¹) x =
      fderiv ℝ (g.pullbackVolumeDensity id) x x /
        (g.pullbackVolumeDensity id x * ‖x‖ ^ 3) := by
  let D := g.leviCivitaData
  let ρ := g.pullbackVolumeDensity id
  let a : E → ℝ := fun y => -(‖y‖ ^ 3)⁻¹
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hnorm : DifferentiableAt ℝ (fun y : E => ‖y‖) x :=
    differentiableAt_id.norm ℝ hx
  have ha := ((hasDerivAt_inv (pow_ne_zero 3 hn)).comp_hasFDerivAt x
    ((hnorm.hasFDerivAt).pow 3)).neg
  change HasFDerivAt a _ x at ha
  have hρ := native_density_smooth_positive g
  have hρa := (hρ.1.differentiable (by simp) x).hasFDerivAt.mul ha
  change HasFDerivAt (fun y : E => ρ y * a y) _ x at hρa
  have hflux (i : Fin 3) :
      (fun y : E => ρ y * WithLp.ofLp (D.gradient (fun z : E => ‖z‖⁻¹) y) i) =ᶠ[𝓝 x]
      (fun y : E => (ρ y * a y) * WithLp.ofLp y i) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    rw [native_gradient_inv_norm g hGauss hy]
    simp [a, mul_assoc]
  have hs : ContDiffAt ℝ ∞ (fun y : E => ‖y‖⁻¹) x :=
    (contDiffAt_norm ℝ hx).inv hn
  have hd := D.density_mul_laplacian_eq_divergence hs
  change ρ x * D.laplacian (fun y : E => ‖y‖⁻¹) x =
    ∑ i : Fin 3, fderiv ℝ
      (fun y : E => ρ y * WithLp.ofLp (D.gradient (fun z : E => ‖z‖⁻¹) y) i) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) at hd
  simp_rw [(hflux _).fderiv_eq] at hd
  rw [LeviCivitaData.sum_fderiv_mul_coordinate hρa.differentiableAt,
    hρa.fderiv] at hd
  simp only [add_apply, smul_apply, smul_eq_mul, neg_apply, Nat.cast_ofNat,
    Nat.reduceSub, hnorm.fderiv_norm_self] at hd
  change -D.laplacian (fun y : E => ‖y‖⁻¹) x = fderiv ℝ ρ x x / (ρ x * ‖x‖ ^ 3)
  have hρne : ρ x ≠ 0 := (hρ.2 x).ne'
  dsimp only [a] at hd
  field_simp [hn, hρne] at hd ⊢
  simp only [nsmul_eq_mul] at hd
  dsimp only [ρ] at hd ⊢
  apply (mul_right_inj' (pow_ne_zero 2 hn)).mp
  nlinarith only [hd]

theorem native_conformalP_inv_norm (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E, g.inner x x v = inner ℝ x v)
    {x : E} (hx : x ≠ 0) :
    -g.leviCivitaData.laplacian (fun y : E => ‖y‖⁻¹) x +
      (g.leviCivitaData.scalarCurvature x / 8) * ‖x‖⁻¹ =
      densityResidual (g.pullbackVolumeDensity id)
        (fun y => g.leviCivitaData.scalarCurvature y / 8) x := by
  rw [native_negative_laplacian_inv_norm g hGauss hx]
  unfold densityResidual
  rw [div_eq_mul_inv (g.leviCivitaData.scalarCurvature x / 8) ‖x‖]

#print axioms native_gradient_inv_norm
#print axioms native_negative_laplacian_inv_norm
#print axioms native_conformalP_inv_norm

end Yamabe3.Analysis.GreenParametrix
