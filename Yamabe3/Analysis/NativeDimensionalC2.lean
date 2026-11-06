/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Geometry/Riemannian/ScalarOperators/Divergence.lean

Carries the coordinate flux product-rule calculation through the three-dimensional C2
development and extends it to arbitrary finite dimension.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.NativeDivergenceC2
import Yamabe3.Analysis.NativeManifoldOperatorC2

/-! Dimension-independent C2 coordinate divergence. Project adaptation
of the verified three-dimensional calculation; the metric is unchanged. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology
namespace Yamabe3.Analysis.NativeDimensionalC2
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
private theorem gradient_eq_inverse_fderiv (g:RiemannianMetric n E)
    (D:LeviCivitaData g) (f:E→ℝ) :
    D.gradient f = fun x=>(g.euclideanCoefficients x).inverse (fderiv ℝ f x) := by
  funext x
  symm
  apply (show (g.euclideanCoefficients x).IsInvertible by convert! g.inner_isInvertible x).inverse_apply_eq.mpr
  ext v
  change (fderiv ℝ f x) v = g.inner x (D.gradient f x) v
  rw [D.inner_gradient]
  simp +instances only [mvfderiv,mfderiv_eq_fderiv,NormedSpace.fromTangentSpace]
  rfl

theorem native_gradient_contDiffAt_C1 (g:RiemannianMetric n E)
    (D:LeviCivitaData g) {f:E→ℝ} {x:E} (hf:ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 1 (D.gradient f) x := by
  rw [gradient_eq_inverse_fderiv]
  have hi:(g.euclideanCoefficients x).IsInvertible:=by convert! g.inner_isInvertible x
  exact ((hi.contDiffAt_map_inverse (n:=1)).comp x
    ((g.contDiffAt_euclideanCoefficients x).of_le (by simp))).clm_apply
    (hf.fderiv_right (by norm_num))

private theorem hessian_gradient_C2 (g:RiemannianMetric n E)
    (D:LeviCivitaData g) {f:E→ℝ} {x:E} (hf:ContDiffAt ℝ 2 f x)
    (u v:TangentSpace (𝓡 n) x) :
    D.hessian f x u v = g.inner x (D.connection (D.gradient f) x u) v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : E→Type _) := ⟨g.toRiemannianMetric⟩
  have hg:MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ,E)) (T% (D.gradient f)) x:=by
    rw [mdifferentiableAt_totalSpace]
    refine ⟨mdifferentiableAt_id, ?_⟩
    simpa using mdifferentiableAt_iff_differentiableAt.mpr
      ((native_gradient_contDiffAt_C1 g D hf).differentiableAt (by norm_num))
  have h:=D.metricCompatible.mvfderiv_inner_eq (FiberBundle.extend E u) hg
    (FiberBundle.mdifferentiableAt_extend (𝓡 n) E v)
  change mvfderiv (𝓡 n) (fun y=>g.inner y (D.gradient f y) (FiberBundle.extend E v y)) x
      (FiberBundle.extend E u x) =
    g.inner x (D.connection (D.gradient f) x (FiberBundle.extend E u x)) (FiberBundle.extend E v x)+
      g.inner x (D.gradient f x) (D.connection (FiberBundle.extend E v) x (FiberBundle.extend E u x)) at h
  simp only [D.inner_gradient,FiberBundle.extend_apply_self] at h
  simpa only [LeviCivitaData.hessian,LeviCivitaData.hessianOnFields,FiberBundle.extend_apply_self] using sub_eq_iff_eq_add.mpr h

theorem native_laplacian_divergence_C2 (g:RiemannianMetric n E)
    (D:LeviCivitaData g) {f:E→ℝ} {x:E} (hf:ContDiffAt ℝ 2 f x) :
    D.laplacian f x = ∑i:Fin n,(fderiv ℝ (D.gradient f) x (EuclideanSpace.basisFun (Fin n) ℝ i)) i+
      ∑i:Fin n,(D.euclideanConnection (EuclideanSpace.basisFun (Fin n) ℝ i) (D.gradient f x) x) i := by
  have hg: DifferentiableAt ℝ (D.gradient f) x:=
    (native_gradient_contDiffAt_C1 g D hf).differentiableAt (by norm_num)
  have ht:D.laplacian f x=LinearMap.trace ℝ (TangentSpace (𝓡 n) x)
      (D.connection (D.gradient f) x).toLinearMap:=by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : E→Type _) := ⟨g.toRiemannianMetric⟩
    rw [LinearMap.trace_eq_sum_inner _ (g.orthonormalBasis x)]
    unfold LeviCivitaData.laplacian
    simp_rw [hessian_gradient_C2 g D hf]
    apply Finset.sum_congr rfl
    intro i _
    exact g.symm x _ _
  rw [ht]
  change LinearMap.trace ℝ E (show E→ₗ[ℝ]E from (D.connection (D.gradient f) x).toLinearMap)=_
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  simp only [Matrix.trace,Matrix.diag,LinearMap.toMatrix_apply,ContinuousLinearMap.coe_coe]
  change (∑i:Fin n,WithLp.ofLp (show E from
    D.connection (D.gradient f) x (EuclideanSpace.basisFun (Fin n) ℝ i)) i)=_
  simp_rw [D.connection_eq_fderiv_add hg]
  exact Finset.sum_add_distrib

private theorem apply_coordinates (L:E→L[ℝ]ℝ) (v:E) :
    L v=∑i:Fin n,L (EuclideanSpace.basisFun (Fin n) ℝ i)*v i:=by
  have h:=congrArg L ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v)
  simpa only [map_sum,map_smul,smul_eq_mul,OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply,EuclideanSpace.basisFun_repr,mul_comm] using h.symm

theorem native_density_laplacian_C2 (g:RiemannianMetric n E)
    (D:LeviCivitaData g) {f:E→ℝ} {x:E} (hf:ContDiffAt ℝ 2 f x) :
    g.pullbackVolumeDensity id x*D.laplacian f x=
      ∑i:Fin n,fderiv ℝ (fun y=>g.pullbackVolumeDensity id y*WithLp.ofLp (D.gradient f y) i)
        x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have hrho:DifferentiableAt ℝ (g.pullbackVolumeDensity id) x:=
    (g.contDiffAt_pullbackVolumeDensity (f:=id) contMDiffAt_id
      (by simpa using Function.injective_id)).1.differentiableAt (by simp)
  have hg: DifferentiableAt ℝ (D.gradient f) x:=
    (native_gradient_contDiffAt_C1 g D hf).differentiableAt (by norm_num)
  have hflux (i:Fin n):
      fderiv ℝ (fun y=>g.pullbackVolumeDensity id y*WithLp.ofLp (D.gradient f y) i)
        x (EuclideanSpace.basisFun (Fin n) ℝ i)=
      fderiv ℝ (g.pullbackVolumeDensity id) x (EuclideanSpace.basisFun (Fin n) ℝ i)*
        WithLp.ofLp (D.gradient f x) i+g.pullbackVolumeDensity id x*
          WithLp.ofLp (fderiv ℝ (D.gradient f) x (EuclideanSpace.basisFun (Fin n) ℝ i)) i:=by
    have hp:=(EuclideanSpace.proj i).hasFDerivAt.comp x hg.hasFDerivAt
    have h:=congrArg (fun L:E→L[ℝ]ℝ=>L (EuclideanSpace.basisFun (Fin n) ℝ i))
      (hrho.hasFDerivAt.mul hp).fderiv
    simpa only [Pi.mul_def,Function.comp_def,add_apply,smul_apply,ContinuousLinearMap.comp_apply,
      smul_eq_mul,EuclideanSpace.coe_proj,mul_comm,add_comm] using! h
  simp_rw [hflux]
  rw [Finset.sum_add_distrib,←apply_coordinates,←Finset.mul_sum,
    D.fderiv_density_eq_connection_trace,native_laplacian_divergence_C2 g D hf]
  ring

#print axioms native_gradient_contDiffAt_C1
#print axioms native_density_laplacian_C2
end Yamabe3.Analysis.NativeDimensionalC2
