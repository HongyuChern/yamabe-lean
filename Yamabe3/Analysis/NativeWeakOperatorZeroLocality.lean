import Yamabe3.Analysis.NativeWeakJacobianLocality
import Yamabe3.Analysis.NativeWeakPhysicalConformalScaling

/-! An actual weak field vanishing on an open set has zero weak
operator there. This uses first/second weak derivative uniqueness,
not pointwise differentiation of an arbitrary representative. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Topology ENNReal BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

 theorem nativeWeakJacobian_zero_of_ae_zero
    {O:Set E} (hO:IsOpen O) {u:E→ℝ} (hu:u=ᵐ[volume.restrict O](fun _=>0))
    (g:RiemannianMetric 3 E) (r:ℝ) (v:ℝ→ℝ) (phase:ℝ):
    nativeWeakRescaledDelaunayJacobian O g r v phase u=ᵐ[volume.restrict O](fun _=>0):=by
  have hp:(1:ℝ≥0∞)≤2:=by norm_num
  have h1(j:Fin 3):chosenWeakPartial' 2 j u O=ᵐ[volume.restrict O](fun _=>0):=
    chosenWeakPartial'_ae_zero_of_ae_zero hp hO hu j
  have h2(i j:Fin 3):chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u O) O=ᵐ[volume.restrict O](fun _=>0):=
    chosenWeakPartial'_ae_zero_of_ae_zero hp hO (h1 j) i
  filter_upwards [hu,eventually_all.mpr h1,eventually_all.mpr (fun i=>eventually_all.mpr (h2 i))] with x hx h1 h2
  simp only [nativeWeakRescaledDelaunayJacobian,weakNegativeLaplacian,iterWeakPartial,
    weakSecondOrderPerturbation,hx,h1,h2,mul_zero,Finset.sum_const_zero,zero_add,sub_zero]
  ring

 theorem nativeGlobalWeakJacobian_zero_on_open
    {u:E→ℝ} (hu:MemWkp 2 2 u univ) {O:Set E} (hO:IsOpen O) (hz:EqOn u (fun _=>0) O)
    (g:RiemannianMetric 3 E) (r:ℝ) (v:ℝ→ℝ) (phase:ℝ):
    nativeWeakRescaledDelaunayJacobian univ g r v phase u=ᵐ[volume.restrict O](fun _=>0):=by
  have he:u=ᵐ[volume.restrict O](fun _=>0):=by
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    exact hz hx
  exact (nativeWeakRescaledDelaunayJacobian_mono hO (subset_univ _) hu g r v phase).trans
    (nativeWeakJacobian_zero_of_ae_zero hO he g r v phase)

 theorem nativeGlobalFullBCF_zero_on_open
    {u:E→ℝ} (hu:MemWkp 2 2 u univ) {O:Set E} (hO:IsOpen O) (hz:EqOn u (fun _=>0) O)
    (g:RiemannianMetric 3 E) (a:ℝ) (V:ℝ→ᵇℝ):
    (fun x=>nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 u x-
      g.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*u x)=ᵐ[volume.restrict O](fun _=>0):=by
  filter_upwards [nativeGlobalWeakJacobian_zero_on_open hu hO hz g a (fun _=>0) 0,
    ae_restrict_mem hO.measurableSet] with x hx hxO
  simp only [hx,hz hxO,mul_zero,sub_self,sub_zero]

#print axioms nativeWeakJacobian_zero_of_ae_zero
#print axioms nativeGlobalWeakJacobian_zero_on_open
#print axioms nativeGlobalFullBCF_zero_on_open
end Yamabe3.Analysis.SpherePolar
