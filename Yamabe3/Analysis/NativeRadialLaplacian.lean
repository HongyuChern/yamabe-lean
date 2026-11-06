import Yamabe3.Analysis.Green.NativeNewtonPointwise

/-!
# Actual radial scalar operator in a Gauss metric

The native gradient and density-divergence formula compute the full radial
Laplacian. The density term is retained: this identity applies to the actual
normal-coordinate metric, without assuming that the metric is flat. It is
the operator input for inserting the constructed periodic end profile into
an arbitrary native background.
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

theorem native_gradient_radial (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E, g.inner x x v = inner ℝ x v)
    (F : ℝ → ℝ) (hF : ContDiffOn ℝ ∞ F (Ioi 0))
    {x : E} (hx : x ≠ 0) :
    g.leviCivitaData.gradient (fun y : E => F ‖y‖) x =
      (deriv F ‖x‖ / ‖x‖) • x := by
  let D := g.leviCivitaData
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hnorm : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y : E => ‖y‖) x :=
    (contDiffAt_norm ℝ hx (n := ∞)).contMDiffAt
  have hgrad : D.gradient (fun y : E => ‖y‖) x = ‖x‖⁻¹ • x := by
    have h := D.gradient_radial_coordinate (OpenPartialHomeomorph.refl E)
      contMDiffOn_id contMDiffOn_id (mem_univ x) hx
      (by intro v; convert! hGauss x v using 1; simp; rfl)
    convert! h using 1
    simp
    rfl
  have hFa := (hF.contDiffAt (isOpen_Ioi.mem_nhds hn)).differentiableAt (by simp)
  have h := D.gradient_comp (hnorm.mdifferentiableAt (by simp)) hFa
  simpa only [Function.comp_def, hgrad, smul_smul, div_eq_mul_inv] using h

theorem native_laplacian_radial (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E, g.inner x x v = inner ℝ x v)
    (F : ℝ → ℝ) (hF : ContDiffOn ℝ ∞ F (Ioi 0))
    {x : E} (hx : x ≠ 0) :
    g.leviCivitaData.laplacian (fun y : E => F ‖y‖) x =
      deriv (deriv F) ‖x‖ +
        (2 / ‖x‖ + fderiv ℝ (g.pullbackVolumeDensity id) x x /
          (g.pullbackVolumeDensity id x * ‖x‖)) * deriv F ‖x‖ := by
  let D := g.leviCivitaData
  let ρ := g.pullbackVolumeDensity id
  let a : E → ℝ := fun y => deriv F ‖y‖ * ‖y‖⁻¹
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hnorm : DifferentiableAt ℝ (fun y : E => ‖y‖) x :=
    differentiableAt_id.norm ℝ hx
  have hFa : ContDiffAt ℝ ∞ F ‖x‖ := hF.contDiffAt (isOpen_Ioi.mem_nhds hp)
  have hFda : DifferentiableAt ℝ (deriv F) ‖x‖ :=
    (hFa.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)
  have ha := (hFda.hasDerivAt.comp_hasFDerivAt x hnorm.hasFDerivAt).mul
    ((hasDerivAt_inv hn).comp_hasFDerivAt x hnorm.hasFDerivAt)
  change HasFDerivAt a _ x at ha
  have hρ := native_density_smooth_positive g
  have hρa := (hρ.1.differentiable (by simp) x).hasFDerivAt.mul ha
  change HasFDerivAt (fun y : E => ρ y * a y) _ x at hρa
  have hflux (i : Fin 3) :
      (fun y : E => ρ y * WithLp.ofLp (D.gradient (fun z : E => F ‖z‖) y) i) =ᶠ[𝓝 x]
      (fun y : E => (ρ y * a y) * WithLp.ofLp y i) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    rw [native_gradient_radial g hGauss F hF hy]
    simp [a, div_eq_mul_inv, mul_assoc]
  have hs : ContDiffAt ℝ ∞ (fun y : E => F ‖y‖) x :=
    hFa.comp x (contDiffAt_norm ℝ hx)
  have hd := D.density_mul_laplacian_eq_divergence hs
  change ρ x * D.laplacian (fun y : E => F ‖y‖) x =
    ∑ i : Fin 3, fderiv ℝ
      (fun y : E => ρ y * WithLp.ofLp (D.gradient (fun z : E => F ‖z‖) y) i) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) at hd
  simp_rw [(hflux _).fderiv_eq] at hd
  rw [LeviCivitaData.sum_fderiv_mul_coordinate hρa.differentiableAt,
    hρa.fderiv] at hd
  simp only [add_apply, smul_apply, smul_eq_mul, Nat.cast_ofNat,
    hnorm.fderiv_norm_self, Function.comp_apply] at hd
  have hρne : ρ x ≠ 0 := (hρ.2 x).ne'
  change D.laplacian (fun y : E => F ‖y‖) x =
    deriv (deriv F) ‖x‖ + (2 / ‖x‖ + fderiv ℝ ρ x x / (ρ x * ‖x‖)) * deriv F ‖x‖
  dsimp only [a] at hd
  field_simp [hn, hρne] at hd ⊢
  dsimp only [ρ] at hd ⊢
  nlinarith only [hd]

#print axioms native_gradient_radial
#print axioms native_laplacian_radial

end Yamabe3.Analysis.GreenParametrix
