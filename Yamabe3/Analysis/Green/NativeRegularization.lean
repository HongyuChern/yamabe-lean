import PoincareLib.Geometry.Riemannian.ScalarOperators.Divergence.Radial
import PoincareLib.Geometry.Riemannian.ScalarOperators.Gradient
import Yamabe3.Analysis.Green.RegularizedNewton
import Yamabe3.Analysis.Green.EuclideanResidual

/-!
# Native radial regularization in a genuine Gauss metric

The regularized Newton potential is evaluated by the actual retained gradient
and Laplacian of a smooth Riemannian metric. The Gauss identity used below is
supplied by the normalized-chart construction, rather than by redefining the
operator or by assuming the wanted point-source equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT
open Yamabe3.RegularizedNewton

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable (g : RiemannianMetric 3 E) (D : LeviCivitaData g)

/-- In a genuine Gauss metric the radial Euclidean gradient is the native
metric gradient. This includes the origin for every positive regularizer. -/
theorem native_gradient_regularizedNewton
    (hGauss : ∀ x v : E, g.inner x x v = inner ℝ x v)
    {ε : ℝ} (hε : 0 < ε) (x : E) :
    D.gradient (potential ε) x =
      -(‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) • x := by
  apply (g.inner_isInvertible x).injective
  ext v
  rw [D.inner_gradient]
  simp only [map_smul, smul_apply, smul_eq_mul, hGauss]
  change mvfderiv (𝓡 3) (potential ε) x v = _
  have hm : mvfderiv (𝓡 3) (potential ε) x v =
      fderiv ℝ (potential ε) x v := by
    simp +instances only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    rfl
  rw [hm, fderiv_potential hε]
  rfl

/-- Exact native operator formula; its first term is the proved positive
Euclidean approximate identity, and its second term is the density error. -/
theorem native_negative_laplacian_regularizedNewton
    (hGauss : ∀ x v : E, g.inner x x v = inner ℝ x v)
    {ε : ℝ} (hε : 0 < ε) (x : E) :
    -D.laplacian (potential ε) x = kernel ε x +
      (fderiv ℝ (g.pullbackVolumeDensity id) x x /
        g.pullbackVolumeDensity id x) *
          (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) := by
  let ρ := g.pullbackVolumeDensity id
  let a : E → ℝ := fun y => -(‖y‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ))
  have hρ := g.contDiffAt_pullbackVolumeDensity (f := id) contMDiffAt_id
    (by simpa using Function.injective_id) (x := x)
  have ha : HasFDerivAt a
      ((3 * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ))) • innerSL ℝ x) x := by
    convert! (hasFDerivAt_radial_rpow hε (-(3 / 2 : ℝ)) x).neg using 1
    norm_num [a]
  have hρa := (hρ.1.differentiableAt (by simp)).hasFDerivAt.mul ha
  change HasFDerivAt (fun y : E => ρ y * a y) _ x at hρa
  have hflux : ∀ i : Fin 3,
      (fun y : E => ρ y * WithLp.ofLp (D.gradient (potential ε) y) i) =
        (fun y : E => (ρ y * a y) * WithLp.ofLp y i) := by
    intro i
    funext y
    rw [native_gradient_regularizedNewton g D hGauss hε]
    simp [a, mul_assoc]
  have hd := D.density_mul_laplacian_eq_divergence
    ((contDiff_potential hε).of_le le_top |>.contDiffAt) (x := x)
  change ρ x * D.laplacian (potential ε) x =
    ∑ i : Fin 3, fderiv ℝ
      (fun y : E => ρ y * WithLp.ofLp (D.gradient (potential ε) y) i) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) at hd
  simp_rw [hflux] at hd
  rw [LeviCivitaData.sum_fderiv_mul_coordinate
    (a := fun y : E => ρ y * a y) hρa.differentiableAt] at hd
  have hEval : fderiv ℝ (fun y => ρ y * a y) x x =
      fderiv ℝ ρ x x * a x +
        ρ x * (3 * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) * ‖x‖ ^ 2) := by
    rw [hρa.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply,
      real_inner_self_eq_norm_sq]
    ring
  rw [hEval] at hd
  have hp : (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) =
      (‖x‖ ^ 2 + ε ^ 2) * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) := by
    calc
      _ = (‖x‖ ^ 2 + ε ^ 2) ^ ((1 : ℝ) + -(5 / 2 : ℝ)) := by norm_num
      _ = _ := by rw [Real.rpow_add (normSq_add_sq_pos hε x), Real.rpow_one]
  have hρne : ρ x ≠ 0 := hρ.2.ne'
  change -D.laplacian (potential ε) x = kernel ε x +
    (fderiv ℝ ρ x x / ρ x) * _
  apply (mul_left_cancel₀ hρne)
  dsimp only [a] at hd
  unfold kernel
  rw [hp] at hd ⊢
  field_simp [hρne]
  nlinarith [hd]

#print axioms native_gradient_regularizedNewton
#print axioms native_negative_laplacian_regularizedNewton

end Yamabe3.Analysis.GreenParametrix
