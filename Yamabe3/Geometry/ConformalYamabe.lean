import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Curvature.Conformal.ConformalScalar
import PoincareLib.Geometry.Riemannian.ScalarOperators.Composition
import PoincareLib.Geometry.Riemannian.ScalarOperators.Scaling
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Yamabe3.Algebra.Normalization

/-!
# Three-dimensional conformal Yamabe formula

The metric is the actual native positive scaling `u^4 g`. The exponential
conformal-change theorem from the pinned PoincareLib is used with `F=-2 log u`.
The logarithmic Laplacian identity is obtained from the global exponential
chain rule, so no log chain rule or curvature identity is assumed as input.
-/

set_option autoImplicit false
open scoped Manifold ContDiff Bundle

namespace Yamabe3.Geometry

open PoincareMT PoincareMT.MetricSurgery

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in
lemma contMDiff_log_of_pos {u : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u) (hpos : ∀ x, 0 < u x) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => Real.log (u x)) := by
  intro x
  exact (Real.contDiffAt_log.mpr (hpos x).ne').contMDiffAt.comp x (hu x)

lemma laplacian_exp_log (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {u : M → ℝ} (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hpos : ∀ x, 0 < u x) (x : M) :
    D.laplacian u x = u x *
      (D.laplacian (fun y => Real.log (u y)) x +
        g.inner x (D.gradient (fun y => Real.log (u y)) x)
          (D.gradient (fun y => Real.log (u y)) x)) := by
  have h := D.laplacian_comp (contMDiff_log_of_pos hu hpos) Real.contDiff_exp x
  simp only [Real.deriv_exp, Function.comp_def] at h
  simp only [Real.exp_log (hpos _)] at h
  rw [h]
  ring

lemma gradient_const_mul (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (c : ℝ) (f : M → ℝ) (x : M) :
    D.gradient (fun y => c * f y) x = c • D.gradient f x := by
  apply (g.inner_isInvertible x).injective
  ext v
  simp only [D.inner_gradient, mvfderiv_const_mul, map_smul, smul_apply, smul_eq_mul]

private lemma scalarCurvature_cast {g h : RiemannianMetric n M}
    (e : g = h) (D : LeviCivitaData h) (x : M) :
    (e.symm ▸ D : LeviCivitaData g).scalarCurvature x = D.scalarCurvature x := by
  cases e
  rfl

lemma exp_neg_two_neg_two_log {r : ℝ} (hr : 0 < r) :
    Real.exp (-2 * (-2 * Real.log r)) = r ^ 4 := by
  rw [show -2 * (-2 * Real.log r) = (4 : ℕ) * Real.log r by ring,
    Real.exp_nat_mul, Real.exp_log hr]

lemma exp_two_neg_two_log {r : ℝ} (hr : 0 < r) :
    Real.exp (2 * (-2 * Real.log r)) = (r ^ 4)⁻¹ := by
  rw [show 2 * (-2 * Real.log r) = -((4 : ℕ) * Real.log r) by ring,
    Real.exp_neg, Real.exp_nat_mul, Real.exp_log hr]

private lemma positiveScaling_congr (g : RiemannianMetric n M)
    {f h : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h)
    (hp : ∀ x, 0 < f x) (hq : ∀ x, 0 < h x) (e : f = h) :
    positiveScaling g f hf hp = positiveScaling g h hh hq := by
  cases e
  rfl

end Yamabe3.Geometry

namespace Yamabe3.Geometry

open PoincareMT PoincareMT.MetricSurgery

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- The scalar curvature of the actual metric `u^4 g`, with the
`div grad` convention for the native Laplacian. -/
theorem scalarCurvature_positiveScaling_pow_four
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {u : M → ℝ} (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hpos : ∀ x, 0 < u x)
    (D' : LeviCivitaData (positiveScaling g (fun y => u y ^ 4)
      (hu.pow 4) (fun y => pow_pos (hpos y) 4))) (x : M) :
    D'.scalarCurvature x = (u x ^ 5)⁻¹ *
      (-8 * D.laplacian u x + D.scalarCurvature x * u x) := by
  let F : M → ℝ := fun y => -2 * Real.log (u y)
  have hF : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F :=
    contMDiff_const.mul (contMDiff_log_of_pos hu hpos)
  have hmetric : positiveScaling g (fun y => Real.exp (-2 * F y))
      (contMDiff_exp_neg_two hF) (fun y => Real.exp_pos _) =
      positiveScaling g (fun y => u y ^ 4) (hu.pow 4)
        (fun y => pow_pos (hpos y) 4) := by
    apply positiveScaling_congr
    funext y
    exact exp_neg_two_neg_two_log (hpos y)
  let Dexp : LeviCivitaData (positiveScaling g
      (fun y => Real.exp (-2 * F y))
      (contMDiff_exp_neg_two hF) (fun y => Real.exp_pos _)) := hmetric.symm ▸ D'
  have hcon := scalarCurvature_positiveScaling_exp g D F hF Dexp x
  have hsc : Dexp.scalarCurvature x = D'.scalarCurvature x :=
    scalarCurvature_cast hmetric D' x
  rw [hsc] at hcon
  simp only [F, D.laplacian_const_mul, gradient_const_mul,
    map_smul, smul_apply, smul_eq_mul] at hcon
  rw [exp_two_neg_two_log (hpos x)] at hcon
  have hlog := laplacian_exp_log g D hu hpos x
  rw [hcon, hlog]
  field_simp
  ring

/-- Constant scalar curvature six is equivalent to the actual singular
Yamabe PDE, before any existence or completeness claim is made. -/
theorem scalarCurvature_eq_six_iff
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {u : M → ℝ} (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hpos : ∀ x, 0 < u x)
    (D' : LeviCivitaData (positiveScaling g (fun y => u y ^ 4)
      (hu.pow 4) (fun y => pow_pos (hpos y) 4))) (x : M) :
    D'.scalarCurvature x = 6 ↔
      -8 * D.laplacian u x + D.scalarCurvature x * u x = 6 * u x ^ 5 := by
  rw [scalarCurvature_positiveScaling_pow_four g D hu hpos D' x,
    inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 5 (hpos x).ne')]
  rw [mul_comm (u x ^ 5) 6]

/-- The manuscript normalization `P_g=-Δ_g+R_g/8` has coefficient `3/4`.
This equivalence uses the native scalar curvature and Laplacian. -/
theorem scalarCurvature_eq_six_iff_normalizedEquation
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {u : M → ℝ} (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hpos : ∀ x, 0 < u x)
    (D' : LeviCivitaData (positiveScaling g (fun y => u y ^ 4)
      (hu.pow 4) (fun y => pow_pos (hpos y) 4))) (x : M) :
    D'.scalarCurvature x = 6 ↔
      -D.laplacian u x + (1 / 8 : ℝ) * D.scalarCurvature x * u x =
        (3 / 4 : ℝ) * u x ^ 5 := by
  rw [scalarCurvature_eq_six_iff g D hu hpos D' x]
  exact (Yamabe3.normalized_equation_iff _ _ _).symm

#print axioms scalarCurvature_positiveScaling_pow_four
#print axioms scalarCurvature_eq_six_iff
#print axioms scalarCurvature_eq_six_iff_normalizedEquation

end Yamabe3.Geometry
