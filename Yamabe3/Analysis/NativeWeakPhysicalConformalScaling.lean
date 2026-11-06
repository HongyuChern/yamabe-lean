import Yamabe3.Analysis.NativeH2ConformalTransposed
import Yamabe3.Analysis.NativeWeakJacobianScaling
import Yamabe3.Analysis.NativeWeakDivergenceJacobian
import Yamabe3.Analysis.EuclideanEnergyDilation

/-! Exact physical scaling of the SAME weak native operator and source.
The native density, scalar curvature, inverse-square orbit term and
factor8 remain explicit. No flatness of the metric is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

theorem nativeWeakJacobian_one_conformal_density
    (O:Set E) (g:RiemannianMetric 3 E) (v:ℝ→ℝ) (phase:ℝ) (u:E→ℝ) (x:E) :
    nativeWeakConformalDensity O g u x=
      8*nativeWeakRescaledDelaunayJacobian O g 1 v phase u x-
        8*g.pullbackVolumeDensity id x*annularDelaunayPotential v phase x*u x := by
  rw [nativeWeakJacobian_eq_divergence]
  simp only [nativeWeakConformalDensity,nativeScaledDivergenceMatrix,one_smul,
    nativeDelaunayPotentialError,one_pow,one_mul,nativePotentialDensity]
  have hc:nativeScaledDivergenceMatrix g 1=nativeDivergenceMatrix g:=by
    ext i j y
    simp only [nativeScaledDivergenceMatrix,one_smul]
  rw [hc]
  ring

theorem nativeWeak_physical_conformal_source
    (g:RiemannianMetric 3 E) (v:ℝ→ℝ) (phase:ℝ)
    {a:ℝ} (ha:0<a) {O:Set E} (hO:IsOpen O) (h0:O⊆({0}ᶜ:Set E))
    {u f:E→ℝ} (hu:MemWkp 2 2 u O)
    (he:nativeWeakRescaledDelaunayJacobian O g a v phase u=ᵐ[volume.restrict O]fun x=>f x/8) :
    let D:=euclideanDilatedDomain a O
    let U:=fun x:E=>u (a⁻¹ • x)
    MemWkp 2 2 U D ∧ nativeWeakConformalDensity D g U=ᵐ[volume.restrict D]
      fun x=>(a⁻¹)^2*f (a⁻¹ • x)-
        8*g.pullbackVolumeDensity id x*annularDelaunayPotential v (phase+Real.log a) x*U x := by
  dsimp only
  have hr:0<a⁻¹:=inv_pos.mpr ha
  have hm:=memWkp_comp_dilation hr.ne' hO (by norm_num: (1:ℝ≥0∞)≤2) 2 hu
  refine ⟨hm,?_⟩
  have hd:=nativeWeakRescaledDelaunayJacobian_dilation hr hO h0 hu g a v phase
  have hs:=ae_comp_dilation hr.ne' he
  rw [mul_inv_cancel₀ ha.ne',Real.log_inv,sub_neg_eq_add] at hd
  filter_upwards [hd,hs] with x hd hs
  change nativeWeakConformalDensity (euclideanDilatedDomain a O) g (fun y:E=>u (a⁻¹ • y)) x=_
  rw [nativeWeakJacobian_one_conformal_density _ g v (phase+Real.log a)]
  change 8*nativeWeakRescaledDelaunayJacobian ((fun x:E=>a⁻¹ • x) ⁻¹' O) g 1 v (phase+Real.log a) (fun y:E=>u (a⁻¹ • y)) x-_= _
  rw [hd,hs]
  ring

#print axioms nativeWeakJacobian_one_conformal_density
#print axioms nativeWeak_physical_conformal_source
end Yamabe3.Analysis.SpherePolar
