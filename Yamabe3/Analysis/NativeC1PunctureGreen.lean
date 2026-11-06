import Yamabe3.Analysis.EuclideanWeakDivergenceRemoval
import Yamabe3.Analysis.NativeEuclideanGreenC2

/-! Actual native Green identity across countably many classical second
 derivative exceptions. The C1 field and integrable classical divergence
 supply the weak identity; the latter is not an input assumption. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff Bundle
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
namespace Yamabe3.Analysis.EuclideanSphereTrace
open UniformElliptic SphereBoundaryLayer GreenParametrix GreenMass.NativeGaussSphereArea

private theorem gradient_eq_inverse_C1 (g:RiemannianMetric 3 E)
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

theorem continuous_native_gradient_C1 (g:RiemannianMetric 3 E)
    {f:E→ℝ} (hf:ContDiff ℝ 1 f) : Continuous (g.leviCivitaData.gradient f) := by
  rw [gradient_eq_inverse_C1]
  apply continuous_iff_continuousAt.mpr
  intro x
  have hi:(g.euclideanCoefficients x).IsInvertible:=by convert! g.inner_isInvertible x
  exact (((hi.contDiffAt_map_inverse (n:=1)).comp x
    ((g.contDiffAt_euclideanCoefficients x).of_le (by simp))).continuousAt).clm_apply
    (hf.continuous_fderiv (by norm_num)).continuousAt

private theorem apply_coordinates_puncture (L:E→L[ℝ]ℝ) (v:E) :
    L v=∑i:Fin 3,L (EuclideanSpace.basisFun (Fin 3) ℝ i)*v i:=by
  have h:=congrArg L ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.sum_repr v)
  simpa only [map_sum,map_smul,smul_eq_mul,OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply,EuclideanSpace.basisFun_repr,mul_comm] using h.symm

theorem integral_native_mul_laplacian_density_off_countable
    (g:RiemannianMetric 3 E) {u φ:E→ℝ}
    (hu:ContDiff ℝ 1 u) {s:Set E} (hs:s.Countable)
    (hu2:∀x∉s,ContDiffAt ℝ 2 u x)
    (hφ:ContDiff ℝ 1 φ) (hc:HasCompactSupport φ)
    (hi:Integrable (fun x=>φ x*g.leviCivitaData.laplacian u x*g.pullbackVolumeDensity id x)) :
    (∫x,φ x*g.leviCivitaData.laplacian u x*g.pullbackVolumeDensity id x)=
    -(∫x,g.inner x (g.leviCivitaData.gradient φ x) (g.leviCivitaData.gradient u x)*
      g.pullbackVolumeDensity id x) := by
  let D:=g.leviCivitaData
  let ρ:=g.pullbackVolumeDensity id
  let Z:E→(Fin 3→ℝ):=fun x i=>ρ x*WithLp.ofLp (D.gradient u x) i
  have hρ:ContDiff ℝ 1 ρ:=contDiff_iff_contDiffAt.mpr fun x=>
    ((g.contDiffAt_pullbackVolumeDensity (f:=id) (x:=x) contMDiffAt_id
      (by simpa using Function.injective_id)).1.of_le (by simp))
  have hZ:Continuous Z:=continuous_pi fun i=>hρ.continuous.mul
    ((show E→L[ℝ]ℝ from EuclideanSpace.proj i).continuous.comp (continuous_native_gradient_C1 g hu))
  have hZ2(x:E)(hx:x∉s):DifferentiableAt ℝ Z x:=by
    apply differentiableAt_pi.mpr
    intro i
    exact (hρ.contDiffAt.mul ((show E→L[ℝ]ℝ from EuclideanSpace.proj i).contDiff.contDiffAt.comp x
      (native_gradient_contDiffAt_C1 g D (hu2 x hx)))).differentiableAt (by norm_num)
  have hdiv(x:E)(hx:x∉s):
      (∑i:Fin 3,fderiv ℝ Z x (EuclideanSpace.single i 1) i)=ρ x*D.laplacian u x:=by
    rw [native_density_laplacian_C2 g D (hu2 x hx)]
    apply Finset.sum_congr rfl
    intro i _
    have hp:=(ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Fin 3=>ℝ) i).hasFDerivAt.comp x (hZ2 x hx).hasFDerivAt
    have he:=congrArg (fun L:E→L[ℝ]ℝ=>L (EuclideanSpace.single i 1)) hp.fderiv
    simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
      EuclideanSpace.basisFun_apply] using he.symm
  have hne:∀ᵐx:E ∂volume,x∉s:=by
    rw [ae_iff]
    simpa only [not_not,Set.setOf_mem_eq] using hs.measure_zero (volume:Measure E)
  have hleft:(fun x:E=>φ x*(∑i:Fin 3,fderiv ℝ Z x (EuclideanSpace.single i 1) i))=ᵐ[volume]
      (fun x=>φ x*D.laplacian u x*ρ x):=by
    filter_upwards [hne] with x hx
    rw [hdiv x hx]
    ring
  have hright(x:E):(∑i:Fin 3,fderiv ℝ φ x (EuclideanSpace.single i 1)*Z x i)=
      g.inner x (D.gradient φ x) (D.gradient u x)*ρ x:=by
    rw [D.inner_gradient]
    simp +instances only [mvfderiv,mfderiv_eq_fderiv,NormedSpace.fromTangentSpace]
    change _=fderiv ℝ φ x (D.gradient u x)*ρ x
    rw [apply_coordinates_puncture,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [EuclideanSpace.basisFun_apply]
    dsimp [Z]
    ring
  have h:=integral_test_divergence_off_countable hZ hs hZ2 hφ hc (hi.congr hleft.symm)
  simpa only [integral_congr_ae hleft,hright] using h

theorem integral_native_mul_laplacian_off_countable
    (g:RiemannianMetric 3 E) {u φ:E→ℝ}
    (hu:ContDiff ℝ 1 u) {s:Set E} (hs:s.Countable)
    (hu2:∀x∉s,ContDiffAt ℝ 2 u x)
    (hφ:ContDiff ℝ 1 φ) (hc:HasCompactSupport φ)
    (hi:Integrable (fun x=>φ x*g.leviCivitaData.laplacian u x*g.pullbackVolumeDensity id x)) :
    (∫x,φ x*g.leviCivitaData.laplacian u x ∂g.volumeMeasure)=
    -(∫x,g.inner x (g.leviCivitaData.gradient φ x) (g.leviCivitaData.gradient u x) ∂g.volumeMeasure) := by
  simp only [native_integral_eq_density g]
  exact integral_native_mul_laplacian_density_off_countable g hu hs hu2 hφ hc hi

#print axioms continuous_native_gradient_C1
#print axioms integral_native_mul_laplacian_density_off_countable
#print axioms integral_native_mul_laplacian_off_countable
end Yamabe3.Analysis.EuclideanSphereTrace
