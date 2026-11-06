import Yamabe3.Analysis.NativeOrbitWeakJacobian
import Yamabe3.Analysis.NativePotentialErrorScaling

/-! Exact dilation of the weak native operator, including mixed second
partials, coefficient divergence, scalar curvature and orbit phase. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

theorem chosenWeakSecond_comp_dilation {r : ℝ} (hr : r≠0) {O : Set E} (hO : IsOpen O)
    {u : E → ℝ} (hu : MemWkp 2 2 u O) (i j : Fin 3) :
    chosenWeakPartial' 2 i (chosenWeakPartial' 2 j (fun x => u (r • x)) ((fun x => r • x) ⁻¹' O))
        ((fun x => r • x) ⁻¹' O)=ᵐ[volume.restrict ((fun x => r • x) ⁻¹' O)]
      (fun x => r^2*chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u O) O (r • x)) := by
  have hp : (1:ℝ≥0∞)≤2 := by norm_num
  have hW : IsOpen ((fun x : E => r • x) ⁻¹' O) := hO.preimage (continuous_id.const_smul r)
  have h1 := chosenWeakPartial_comp_dilation hr hO hu.le_succ j
  have h2 := chosenWeakPartial_comp_dilation hr hO (hu.chosenWeakPartial_mem j) i
  have hc := memWkp_comp_dilation hr hO hp 1 (hu.chosenWeakPartial_mem j)
  have he := (chosenWeakPartial'_ae_congr hp hW h1 i).trans
    (chosenWeakPartial'_const_smul_ae hp hW hc.memW1p r i)
  filter_upwards [he,h2] with x hx hy
  rw [hx,hy]
  ring

theorem nativeScaledPrincipalError_dilation (g : RiemannianMetric 3 E) (ε r : ℝ) (i j : Fin 3) (x : E) :
    nativeScaledPrincipalError g (ε*r) i j x=nativeScaledPrincipalError g ε i j (r • x) := by
  simp only [nativeScaledPrincipalError,smul_smul]

theorem nativeScaledFirstError_dilation (g : RiemannianMetric 3 E) (ε r : ℝ) (j : Fin 3) (x : E) :
    nativeScaledFirstError g (ε*r) j x=r*nativeScaledFirstError g ε j (r • x) := by
  have hc (i : Fin 3) : nativeScaledPrincipalError g (ε*r) i j=
      (fun y => nativeScaledPrincipalError g ε i j (r • y)) :=
    funext (nativeScaledPrincipalError_dilation g ε r i j)
  simp only [nativeScaledFirstError,hc,partialDeriv,fderiv_comp_smul,smul_apply,smul_eq_mul,Finset.mul_sum]

theorem nativeWeakRescaledDelaunayJacobian_dilation
    {r : ℝ} (hr : 0<r) {O : Set E} (hO : IsOpen O) (h0 : O⊆({0}ᶜ : Set E))
    {u : E → ℝ} (hu : MemWkp 2 2 u O) (g : RiemannianMetric 3 E) (ε : ℝ) (v : ℝ → ℝ) (phase : ℝ) :
    nativeWeakRescaledDelaunayJacobian ((fun x => r • x) ⁻¹' O) g (ε*r) v (phase-Real.log r)
      (fun x => u (r • x))=ᵐ[volume.restrict ((fun x => r • x) ⁻¹' O)]
      (fun x => r^2*nativeWeakRescaledDelaunayJacobian O g ε v phase u (r • x)) := by
  have h1 (j : Fin 3) := chosenWeakPartial_comp_dilation hr.ne' hO hu.le_succ j
  have h2 (i j : Fin 3) := chosenWeakSecond_comp_dilation hr.ne' hO hu i j
  have hW : IsOpen ((fun x : E => r • x) ⁻¹' O) := hO.preimage (continuous_id.const_smul r)
  filter_upwards [eventually_all.mpr h1,eventually_all.mpr (fun i => eventually_all.mpr (h2 i)),
    weakNegativeLaplacian_comp_dilation hr.ne' hO hu,ae_restrict_mem hW.measurableSet] with x h1 h2 hl hx
  have hx0 : x≠0 := by intro he;apply h0 hx;simpa only [he,smul_zero,mem_singleton_iff]
  have hQ : annularDelaunayPotential v (phase-Real.log r) x=r^2*annularDelaunayPotential v phase (r • x) := by
    unfold annularDelaunayPotential
    rw [norm_smul,Real.norm_of_nonneg hr.le,Real.log_mul hr.ne' (norm_ne_zero_iff.mpr hx0)]
    rw [show phase-(Real.log r+Real.log ‖x‖)=phase-Real.log r-Real.log ‖x‖ by ring]
    field_simp [hr.ne',norm_ne_zero_iff.mpr hx0]
    <;> ring
  have hP := nativeDelaunayPotentialError_scale g ε v phase hr hx0
  simp only [nativeWeakRescaledDelaunayJacobian,hl,weakSecondOrderPerturbation,h1,h2,
    nativeScaledPrincipalError_dilation,nativeScaledFirstError_dilation,hQ,←hP,zero_mul,add_zero]
  simp only [Fin.sum_univ_three]
  ring

#print axioms chosenWeakSecond_comp_dilation
#print axioms nativeScaledPrincipalError_dilation
#print axioms nativeScaledFirstError_dilation
#print axioms nativeWeakRescaledDelaunayJacobian_dilation
end Yamabe3.Analysis.SpherePolar
