import Yamabe3.Analysis.UniformElliptic.UniformDivergenceHessian
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Exact rescaling of the actual divergence operator

These identities use actual totalized Frechet derivatives. Scalar dilation,
nonzero scalar multiplication (and its zero case), and subtraction of a
constant preserve their exact transformation formulas even without a global
smoothness premise. Local regularity is imposed separately when using PDEs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem partial_comp_smul (u : E → ℝ) (r : ℝ) (j : Fin d) (x : E) :
    partialDeriv j (fun y => u (r • y)) x = r * partialDeriv j u (r • x) := by
  unfold partialDeriv
  rw [fderiv_comp_smul]
  simp only [smul_apply, smul_eq_mul]

private theorem partial_const_mul (u : E → ℝ) (c : ℝ) (j : Fin d) (x : E) :
    partialDeriv j (fun y => c * u y) x = c * partialDeriv j u x := by
  change fderiv ℝ (c • u) x (EuclideanSpace.single j 1) = _
  rw [fderiv_const_smul_field]
  rfl

private theorem partial_sub_const (u : E → ℝ) (b : ℝ) (j : Fin d) (x : E) :
    partialDeriv j (fun y => u y - b) x = partialDeriv j u x := by
  unfold partialDeriv
  rw [fderiv_sub_const]

/-- Exact first derivative of the affine-normalized rescaled function. -/
theorem partial_scaled_centered (u : E → ℝ) (r c b : ℝ) (j : Fin d) (x : E) :
    partialDeriv j (fun y => c * (u (r • y) - b)) x =
      c * r * partialDeriv j u (r • x) := by
  rw [partial_const_mul, partial_sub_const, partial_comp_smul]
  ring

/-- Exact negative-divergence source under the true coefficient rescaling. -/
theorem principalSource_scaled_centered
    (a : E → Matrix (Fin d) (Fin d) ℝ) (u : E → ℝ) (r c b : ℝ) (x : E) :
    principalSource (fun y => a (r • y)) (fun y => c * (u (r • y) - b)) x =
      c * r ^ 2 * principalSource a u (r • x) := by
  have hflux (i : Fin d) :
      matrixFlux (fun y => a (r • y))
        (fun j => partialDeriv j (fun y => c * (u (r • y) - b))) i =
      fun y => (c * r) * matrixFlux a (fun j => partialDeriv j u) i (r • y) := by
    funext y
    unfold matrixFlux
    simp_rw [partial_scaled_centered]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold principalSource
  simp_rw [hflux, partial_const_mul, partial_comp_smul]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

/-- The actual divergence operator depends only on the scalar germ, with
no free source-equivalence hypothesis. -/
theorem principalSource_eq_of_eventuallyEq
    (a : E → Matrix (Fin d) (Fin d) ℝ) {u v : E → ℝ} {x : E}
    (h : u =ᶠ[𝓝 x] v) : principalSource a u x = principalSource a v x := by
  have hp (j : Fin d) : partialDeriv j u =ᶠ[𝓝 x] partialDeriv j v := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun A : E →L[ℝ] ℝ => A (EuclideanSpace.single j 1)) hy
  have hflux (i : Fin d) : matrixFlux a (fun j => partialDeriv j u) i =ᶠ[𝓝 x]
      matrixFlux a (fun j => partialDeriv j v) i := by
    filter_upwards [eventually_all.mpr hp] with y hy
    simp only [matrixFlux, hy]
  unfold principalSource
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun A : E →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) (hflux i).fderiv_eq

#print axioms partial_scaled_centered
#print axioms principalSource_scaled_centered
#print axioms principalSource_eq_of_eventuallyEq

end Yamabe3.Analysis.UniformElliptic
