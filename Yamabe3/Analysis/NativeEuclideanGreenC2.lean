import Yamabe3.Analysis.NativeDivergenceC2
import Yamabe3.Analysis.NativeExteriorSphereGreen

/-! C2 Green identity for the actual smooth native metric on Euclidean
coordinates. The divergence calculation is used at C2 regularity; no
unproved infinite smoothness of an H4 solver representative is inserted. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff Bundle
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
namespace Yamabe3.Analysis.EuclideanSphereTrace
open UniformElliptic SphereBoundaryLayer GreenParametrix GreenMass.NativeGaussSphereArea

private theorem apply_coordinates_C2 (L:E→L[ℝ]ℝ) (v:E) :
    L v=∑i:Fin 3,L (EuclideanSpace.basisFun (Fin 3) ℝ i)*v i:=by
  have h:=congrArg L ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.sum_repr v)
  simpa only [map_sum,map_smul,smul_eq_mul,OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply,EuclideanSpace.basisFun_repr,mul_comm] using h.symm

theorem continuous_native_gradient_C2 (g:RiemannianMetric 3 E)
    {f:E→ℝ} (hf:ContDiff ℝ 2 f) : Continuous (g.leviCivitaData.gradient f) :=
  continuous_iff_continuousAt.mpr fun x=>
    (native_gradient_contDiffAt_C1 g g.leviCivitaData (hf.contDiffAt (x:=x))).continuousAt

theorem continuous_native_laplacian_C2 (g:RiemannianMetric 3 E)
    {f:E→ℝ} (hf:ContDiff ℝ 2 f) : Continuous (g.leviCivitaData.laplacian f) := by
  let D:=g.leviCivitaData
  let ρ:=g.pullbackVolumeDensity id
  let V:Fin 3→E→ℝ:=fun i x=>ρ x*WithLp.ofLp (D.gradient f x) i
  have hρ:ContDiff ℝ 1 ρ:=contDiff_iff_contDiffAt.mpr fun x=>
    ((g.contDiffAt_pullbackVolumeDensity (f:=id) (x:=x) contMDiffAt_id
      (by simpa using Function.injective_id)).1.of_le (by simp))
  have hV(i:Fin 3):ContDiff ℝ 1 (V i):=contDiff_iff_contDiffAt.mpr fun x=>
    hρ.contDiffAt.mul ((show E→L[ℝ]ℝ from EuclideanSpace.proj i).contDiff.contDiffAt.comp x
      (native_gradient_contDiffAt_C1 g D hf.contDiffAt))
  have hρpos(x:E):0<ρ x:=(g.contDiffAt_pullbackVolumeDensity (f:=id) (x:=x)
    contMDiffAt_id (by simpa using Function.injective_id)).2
  have heq:D.laplacian f=fun x=>(∑i:Fin 3,fderiv ℝ (V i) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i))/ρ x:=by
    funext x
    rw [eq_div_iff (ne_of_gt (hρpos x))]
    exact (mul_comm _ _).trans (native_density_laplacian_C2 g D (hf.contDiffAt (x:=x)))
  rw [heq]
  exact (continuous_finset_sum _ fun i _=>(hV i).continuous_fderiv (by norm_num) |>.clm_apply continuous_const).div
    hρ.continuous (fun x=>(hρpos x).ne')

theorem continuous_native_inner_gradient_C2 (g:RiemannianMetric 3 E)
    {u v:E→ℝ} (hu:ContDiff ℝ 2 u) (hv:ContDiff ℝ 2 v) :
    Continuous (fun x=>g.inner x (g.leviCivitaData.gradient u x) (g.leviCivitaData.gradient v x)) := by
  have heq:(fun x=>g.inner x (g.leviCivitaData.gradient u x) (g.leviCivitaData.gradient v x))=
      fun x=>fderiv ℝ u x (g.leviCivitaData.gradient v x):=by
    funext x
    rw [g.leviCivitaData.inner_gradient]
    simp +instances only [mvfderiv,mfderiv_eq_fderiv,NormedSpace.fromTangentSpace]
    rfl
  rw [heq]
  exact (hu.continuous_fderiv (by norm_num)).clm_apply (continuous_native_gradient_C2 g hv)

theorem integral_native_mul_laplacian_density_C2 (g:RiemannianMetric 3 E)
    {u v:E→ℝ} (hu:ContDiff ℝ 2 u) (hv:ContDiff ℝ 2 v) (hc:HasCompactSupport u) :
    (∫x,u x*g.leviCivitaData.laplacian v x*g.pullbackVolumeDensity id x)=
    -(∫x,g.inner x (g.leviCivitaData.gradient u x) (g.leviCivitaData.gradient v x)*
      g.pullbackVolumeDensity id x) := by
  let D:=g.leviCivitaData
  let V:Fin 3→E→ℝ:=fun i x=>g.pullbackVolumeDensity id x*WithLp.ofLp (D.gradient v x) i
  have hV(i:Fin 3)(x:E):ContDiffAt ℝ 1 (V i) x:=by
    have hρ:=(g.contDiffAt_pullbackVolumeDensity (f:=id) (x:=x) contMDiffAt_id
      (by simpa using Function.injective_id)).1
    exact (hρ.of_le (by simp)).mul ((show E→L[ℝ]ℝ from EuclideanSpace.proj i).contDiff.contDiffAt.comp x
      (native_gradient_contDiffAt_C1 g D hv.contDiffAt))
  have h:=Poincare.integral_mul_coordinate_divergence (hu.of_le (by norm_num)) hc
    (fun i x _=>hV i x)
  have hl(x:E):u x*(∑i:Fin 3,fderiv ℝ (V i) x (EuclideanSpace.basisFun (Fin 3) ℝ i))=
      u x*D.laplacian v x*g.pullbackVolumeDensity id x:=by
    rw [←native_density_laplacian_C2 g D hv.contDiffAt]
    ring
  have hr(x:E):(∑i:Fin 3,fderiv ℝ u x (EuclideanSpace.basisFun (Fin 3) ℝ i)*V i x)=
      g.inner x (D.gradient u x) (D.gradient v x)*g.pullbackVolumeDensity id x:=by
    rw [D.inner_gradient]
    simp +instances only [mvfderiv,mfderiv_eq_fderiv,NormedSpace.fromTangentSpace]
    change _=fderiv ℝ u x (D.gradient v x)*g.pullbackVolumeDensity id x
    rw [apply_coordinates_C2,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [V]
    ring
  simpa only [hl,hr] using h

theorem integral_native_mul_laplacian_C2 (g:RiemannianMetric 3 E)
    {u v:E→ℝ} (hu:ContDiff ℝ 2 u) (hv:ContDiff ℝ 2 v) (hc:HasCompactSupport u) :
    (∫x,u x*g.leviCivitaData.laplacian v x ∂g.volumeMeasure)=
    -(∫x,g.inner x (g.leviCivitaData.gradient u x) (g.leviCivitaData.gradient v x) ∂g.volumeMeasure) := by
  simp only [native_integral_eq_density g]
  exact integral_native_mul_laplacian_density_C2 g hu hv hc

theorem integrable_native_inner_gradient_C2 (g:RiemannianMetric 3 E)
    {u v:E→ℝ} (hu:ContDiff ℝ 2 u) (hv:ContDiff ℝ 2 v) (hc:HasCompactSupport u) :
    Integrable (fun x=>g.inner x (g.leviCivitaData.gradient u x)
      (g.leviCivitaData.gradient v x)) g.volumeMeasure := by
  apply (continuous_native_inner_gradient_C2 g hu hv).integrable_of_hasCompactSupport
  exact g.leviCivitaData.hasCompactSupport_inner_gradient hc v

#print axioms integral_native_mul_laplacian_C2
#print axioms continuous_native_laplacian_C2
#print axioms integrable_native_inner_gradient_C2
end Yamabe3.Analysis.EuclideanSphereTrace
