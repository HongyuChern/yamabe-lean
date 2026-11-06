import Yamabe3.Analysis.UniformElliptic.NativeDelaunayJacobianIdentity

/-! The retained Levi-Civita Laplacian identity at the actual C2
regularity of the solved H4 field. No smoothness upgrade is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter
open scoped Manifold ContDiff Bundle Topology
namespace Yamabe3.Analysis.UniformElliptic
open PoincareMT
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

private theorem gradient_eq_inverse_fderiv (g:RiemannianMetric 3 E)
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

theorem native_gradient_contDiffAt_C1 (g:RiemannianMetric 3 E)
    (D:LeviCivitaData g) {f:E→ℝ} {x:E} (hf:ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 1 (D.gradient f) x := by
  rw [gradient_eq_inverse_fderiv]
  have hi:(g.euclideanCoefficients x).IsInvertible:=by convert! g.inner_isInvertible x
  exact ((hi.contDiffAt_map_inverse (n:=1)).comp x
    ((g.contDiffAt_euclideanCoefficients x).of_le (by simp))).clm_apply
    (hf.fderiv_right (by norm_num))

private theorem hessian_gradient_C2 (g:RiemannianMetric 3 E)
    (D:LeviCivitaData g) {f:E→ℝ} {x:E} (hf:ContDiffAt ℝ 2 f x)
    (u v:TangentSpace (𝓡 3) x) :
    D.hessian f x u v = g.inner x (D.connection (D.gradient f) x u) v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : E→Type _) := ⟨g.toRiemannianMetric⟩
  have hg:MDifferentiableAt (𝓡 3) ((𝓡 3).prod 𝓘(ℝ,E)) (T% (D.gradient f)) x:=by
    rw [mdifferentiableAt_totalSpace]
    refine ⟨mdifferentiableAt_id, ?_⟩
    simpa using mdifferentiableAt_iff_differentiableAt.mpr
      ((native_gradient_contDiffAt_C1 g D hf).differentiableAt (by norm_num))
  have h:=D.metricCompatible.mvfderiv_inner_eq (FiberBundle.extend E u) hg
    (FiberBundle.mdifferentiableAt_extend (𝓡 3) E v)
  change mvfderiv (𝓡 3) (fun y=>g.inner y (D.gradient f y) (FiberBundle.extend E v y)) x
      (FiberBundle.extend E u x) =
    g.inner x (D.connection (D.gradient f) x (FiberBundle.extend E u x)) (FiberBundle.extend E v x)+
      g.inner x (D.gradient f x) (D.connection (FiberBundle.extend E v) x (FiberBundle.extend E u x)) at h
  simp only [D.inner_gradient,FiberBundle.extend_apply_self] at h
  simpa only [LeviCivitaData.hessian,LeviCivitaData.hessianOnFields,FiberBundle.extend_apply_self] using sub_eq_iff_eq_add.mpr h

theorem native_laplacian_divergence_C2 (g:RiemannianMetric 3 E)
    (D:LeviCivitaData g) {f:E→ℝ} {x:E} (hf:ContDiffAt ℝ 2 f x) :
    D.laplacian f x = ∑i:Fin 3,(fderiv ℝ (D.gradient f) x (EuclideanSpace.basisFun (Fin 3) ℝ i)) i+
      ∑i:Fin 3,(D.euclideanConnection (EuclideanSpace.basisFun (Fin 3) ℝ i) (D.gradient f x) x) i := by
  have hg: DifferentiableAt ℝ (D.gradient f) x:=
    (native_gradient_contDiffAt_C1 g D hf).differentiableAt (by norm_num)
  have ht:D.laplacian f x=LinearMap.trace ℝ (TangentSpace (𝓡 3) x)
      (D.connection (D.gradient f) x).toLinearMap:=by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : E→Type _) := ⟨g.toRiemannianMetric⟩
    rw [LinearMap.trace_eq_sum_inner _ (g.orthonormalBasis x)]
    unfold LeviCivitaData.laplacian
    simp_rw [hessian_gradient_C2 g D hf]
    apply Finset.sum_congr rfl
    intro i _
    exact g.symm x _ _
  rw [ht]
  change LinearMap.trace ℝ E (show E→ₗ[ℝ]E from (D.connection (D.gradient f) x).toLinearMap)=_
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp only [Matrix.trace,Matrix.diag,LinearMap.toMatrix_apply,ContinuousLinearMap.coe_coe]
  change (∑i:Fin 3,WithLp.ofLp (show E from
    D.connection (D.gradient f) x (EuclideanSpace.basisFun (Fin 3) ℝ i)) i)=_
  simp_rw [D.connection_eq_fderiv_add hg]
  exact Finset.sum_add_distrib

private theorem apply_coordinates (L:E→L[ℝ]ℝ) (v:E) :
    L v=∑i:Fin 3,L (EuclideanSpace.basisFun (Fin 3) ℝ i)*v i:=by
  have h:=congrArg L ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.sum_repr v)
  simpa only [map_sum,map_smul,smul_eq_mul,OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply,EuclideanSpace.basisFun_repr,mul_comm] using h.symm

theorem native_density_laplacian_C2 (g:RiemannianMetric 3 E)
    (D:LeviCivitaData g) {f:E→ℝ} {x:E} (hf:ContDiffAt ℝ 2 f x) :
    g.pullbackVolumeDensity id x*D.laplacian f x=
      ∑i:Fin 3,fderiv ℝ (fun y=>g.pullbackVolumeDensity id y*WithLp.ofLp (D.gradient f y) i)
        x (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  have hrho:DifferentiableAt ℝ (g.pullbackVolumeDensity id) x:=
    (g.contDiffAt_pullbackVolumeDensity (f:=id) contMDiffAt_id
      (by simpa using Function.injective_id)).1.differentiableAt (by simp)
  have hg: DifferentiableAt ℝ (D.gradient f) x:=
    (native_gradient_contDiffAt_C1 g D hf).differentiableAt (by norm_num)
  have hflux (i:Fin 3):
      fderiv ℝ (fun y=>g.pullbackVolumeDensity id y*WithLp.ofLp (D.gradient f y) i)
        x (EuclideanSpace.basisFun (Fin 3) ℝ i)=
      fderiv ℝ (g.pullbackVolumeDensity id) x (EuclideanSpace.basisFun (Fin 3) ℝ i)*
        WithLp.ofLp (D.gradient f x) i+g.pullbackVolumeDensity id x*
          WithLp.ofLp (fderiv ℝ (D.gradient f) x (EuclideanSpace.basisFun (Fin 3) ℝ i)) i:=by
    have hp:=(EuclideanSpace.proj i).hasFDerivAt.comp x hg.hasFDerivAt
    have h:=congrArg (fun L:E→L[ℝ]ℝ=>L (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (hrho.hasFDerivAt.mul hp).fderiv
    simpa only [Pi.mul_def,Function.comp_def,add_apply,smul_apply,ContinuousLinearMap.comp_apply,
      smul_eq_mul,EuclideanSpace.coe_proj,mul_comm,add_comm] using! h
  simp_rw [hflux]
  rw [Finset.sum_add_distrib,←apply_coordinates,←Finset.mul_sum,
    D.fderiv_density_eq_connection_trace,native_laplacian_divergence_C2 g D hf]
  ring

theorem native_principalSource_eq_negative_density_laplacian_C2
    (g:RiemannianMetric 3 E) (D:LeviCivitaData g) {f:E→ℝ} {x:E}
    (hf:ContDiffAt ℝ 2 f x) :
    principalSource (nativeDivergenceMatrix g) f x = -g.pullbackVolumeDensity id x*D.laplacian f x:=by
  have hflux (i:Fin 3):(fun y:E=>g.pullbackVolumeDensity id y*WithLp.ofLp (D.gradient f y) i)=
      matrixFlux (nativeDivergenceMatrix g) (fun j=>partialDeriv j f) i:=by
    funext y
    exact (matrixFlux_native_eq_density_gradient g D f i y).symm
  have hd:=native_density_laplacian_C2 g D hf
  simp_rw [hflux,EuclideanSpace.basisFun_apply] at hd
  change -(∑i:Fin 3,partialDeriv i (matrixFlux (nativeDivergenceMatrix g) (fun j=>partialDeriv j f) i) x)=_
  change g.pullbackVolumeDensity id x*D.laplacian f x=
    ∑i:Fin 3,partialDeriv i (matrixFlux (nativeDivergenceMatrix g) (fun j=>partialDeriv j f) i) x at hd
  linarith

#print axioms native_gradient_contDiffAt_C1
#print axioms native_laplacian_divergence_C2
#print axioms native_density_laplacian_C2
#print axioms native_principalSource_eq_negative_density_laplacian_C2
end Yamabe3.Analysis.UniformElliptic
