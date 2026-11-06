/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Geometry/Riemannian/Distance/Smoothing/Minimum.lean

Adapts the Hessian addition proof for the Laplacian and the first variation of the
Yamabe expression.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import PoincareLib.Geometry.Riemannian.ScalarOperators.Linearity
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# The actual native Yamabe first variation

Local smooth germs suffice for native Hessian and Laplacian additivity.
The real derivative of the actual nonlinear scalar expression along
u + a*psi is then the genuine native linearized operator.  No abstract
linearization or global smooth extension is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter PoincareMT
open scoped Manifold ContDiff Bundle Topology

namespace Yamabe3.Analysis.YamabeVariation

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem native_hessian_add_at (D : LeviCivitaData g) {f h : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hh : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ h x)
    (u v : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => f y + h y) x u v = D.hessian f x u v + D.hessian h x u v := by
  have hf1 := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  have hh1 := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hh.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  have hgrad : D.gradient (fun y => f y + h y) =ᶠ[𝓝 x] D.gradient f + D.gradient h := by
    filter_upwards [hf1, hh1] with y hyf hyh
    exact D.gradient_add (hyf.mdifferentiableAt (by simp)) (hyh.mdifferentiableAt (by simp))
  have hfh : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => f y + h y) x := by
    simpa only [Pi.add_def] using hf.add hh
  have hs := (D.contMDiffAt_gradient hfh).mdifferentiableAt (by simp)
  have hsum : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% (D.gradient f + D.gradient h)) x := by
    apply hs.congr_of_eventuallyEq
    filter_upwards [hgrad] with y hy
    simp only [← hy]
  have hc := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hs hsum (by simp) hgrad
  rw [D.hessian_eq_inner_connection_gradient hfh,
    D.hessian_eq_inner_connection_gradient hf, D.hessian_eq_inner_connection_gradient hh,
    congrArg (fun L => L u) hc,
    D.connection.isCovariantDerivativeOn.add
      ((D.contMDiffAt_gradient hf).mdifferentiableAt (by simp))
      ((D.contMDiffAt_gradient hh).mdifferentiableAt (by simp))]
  simp only [add_apply, map_add]

theorem native_laplacian_add_at (D : LeviCivitaData g) {f h : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hh : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ h x) :
    D.laplacian (fun y => f y + h y) x = D.laplacian f x + D.laplacian h x := by
  simp only [LeviCivitaData.laplacian, native_hessian_add_at D hf hh, Finset.sum_add_distrib]

theorem native_yamabe_hasDerivAt (D : LeviCivitaData g) {u ψ : M → ℝ} {x : M}
    (hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ u x)
    (hψ : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ x) :
    HasDerivAt (fun a : ℝ =>
      -8 * D.laplacian (fun y => u y + a * ψ y) x +
        D.scalarCurvature x * (u x + a * ψ x) - 6 * (u x + a * ψ x) ^ 5)
      (-8 * D.laplacian ψ x + D.scalarCurvature x * ψ x - 30 * u x ^ 4 * ψ x) 0 := by
  have heq : (fun a : ℝ =>
      -8 * D.laplacian (fun y => u y + a * ψ y) x +
        D.scalarCurvature x * (u x + a * ψ x) - 6 * (u x + a * ψ x) ^ 5) =
      fun a : ℝ => -8 * (D.laplacian u x + a * D.laplacian ψ x) +
        D.scalarCurvature x * (u x + a * ψ x) - 6 * (u x + a * ψ x) ^ 5 := by
    funext a
    have ha : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => a * ψ y) x := by
      simpa only [Pi.mul_def] using
        (contMDiffAt_const : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun _ : M => a) x).mul hψ
    rw [native_laplacian_add_at D hu ha, D.laplacian_const_mul]
  rw [heq]
  have hv : HasDerivAt (fun a : ℝ => u x + a * ψ x) (ψ x) 0 := by
    simpa only [one_mul, zero_add, Pi.add_def, id_eq] using
      (hasDerivAt_const 0 (u x)).add ((hasDerivAt_id 0).mul_const (ψ x))
  have hL : HasDerivAt (fun a : ℝ => D.laplacian u x + a * D.laplacian ψ x)
      (D.laplacian ψ x) 0 := by
    simpa only [one_mul, zero_add, Pi.add_def, id_eq] using
      (hasDerivAt_const 0 (D.laplacian u x)).add
        ((hasDerivAt_id 0).mul_const (D.laplacian ψ x))
  convert! ((hL.const_mul (-8)).add (hv.const_mul (D.scalarCurvature x))).sub
    ((hv.pow 5).const_mul 6) using 1 <;> norm_num [Pi.add_def, Pi.sub_def] <;> ring

#print axioms native_hessian_add_at
#print axioms native_laplacian_add_at
#print axioms native_yamabe_hasDerivAt

end Yamabe3.Analysis.YamabeVariation
