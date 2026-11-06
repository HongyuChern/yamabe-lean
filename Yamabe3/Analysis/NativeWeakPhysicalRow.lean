import Yamabe3.Analysis.NativeWeakJacobianScaling
import Yamabe3.Analysis.NativeAllScaleLocalH2

/-! A true weak native operator on the physical open window equals its
scaled collar row. The result uses the same H2 function and transports
volume-a.e. identities by the actual dilation map. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

theorem nativeWeakRescaledDelaunayJacobian_const_mul {O : Set E} (hO : IsOpen O)
    {u : E → ℝ} (hu : MemWkp 2 2 u O) (g : RiemannianMetric 3 E) (r : ℝ)
    (v : ℝ → ℝ) (phase c : ℝ) :
    nativeWeakRescaledDelaunayJacobian O g r v phase (fun x => c*u x)=ᵐ[volume.restrict O]
      (fun x => c*nativeWeakRescaledDelaunayJacobian O g r v phase u x) := by
  have hp : (1:ℝ≥0∞)≤2 := by norm_num
  have h1 (j : Fin 3) := chosenWeakPartial'_const_smul_ae hp hO hu.memW1p c j
  have h2 (i j : Fin 3) := (chosenWeakPartial'_ae_congr hp hO (h1 j) i).trans
    (chosenWeakPartial'_const_smul_ae hp hO (hu.chosenWeakPartial_mem j).memW1p c i)
  filter_upwards [eventually_all.mpr h1,eventually_all.mpr (fun i => eventually_all.mpr (h2 i)),
    weakNegativeLaplacian_const_mul hO hu c] with x h1 h2 hl
  simp only [nativeWeakRescaledDelaunayJacobian,hl,weakSecondOrderPerturbation,h1,h2,
    Fin.sum_univ_three,zero_mul,add_zero]
  ring

theorem nativeWeakPhysicalRow_identity (g : RiemannianMetric 3 E) (ε : ℝ)
    (v : ℝ → ℝ) (phase s : ℝ) {u : E → ℝ}
    (hu : MemWkp 2 2 (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • x)) nativePoissonEntranceCollar) :
    (fun x => Real.exp (s/2)*nativeWeakRescaledDelaunayJacobian nativePoissonEntranceCollar g
      (ε*Real.exp (-s)) v (phase+s) (fun y => Real.exp (3*s/2)*u (Real.exp (-s) • y)) (Real.exp s • x))
      =ᵐ[volume.restrict (nativePhysicalScaleWindow s)]
      nativeWeakRescaledDelaunayJacobian (nativePhysicalScaleWindow s) g ε v phase u := by
  have hO := nativePolarTimeWindow_open (1/2)
  have h0 : nativePoissonEntranceCollar⊆({0}ᶜ : Set E) := fun x hx => hx.1
  have hd := nativeWeakRescaledDelaunayJacobian_dilation (Real.exp_pos s) hO h0 hu g
    (ε*Real.exp (-s)) v (phase+s)
  have hscale : ε*Real.exp (-s)*Real.exp s=ε := by rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
  have hfun : (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • (Real.exp s • x)))=
      (fun x => Real.exp (3*s/2)*u x) := by
    funext x
    rw [smul_smul,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_smul]
  rw [hscale,Real.log_exp,add_sub_cancel_right,hfun] at hd
  change nativeWeakRescaledDelaunayJacobian (nativePhysicalScaleWindow s) g ε v phase
      (fun x => Real.exp (3*s/2)*u x)=ᵐ[volume.restrict (nativePhysicalScaleWindow s)]
      (fun x => Real.exp s^2*nativeWeakRescaledDelaunayJacobian nativePoissonEntranceCollar g
        (ε*Real.exp (-s)) v (phase+s) (fun y => Real.exp (3*s/2)*u (Real.exp (-s) • y)) (Real.exp s • x)) at hd
  have hm := native_scaled_H2_to_physical s hu
  have hc := nativeWeakRescaledDelaunayJacobian_const_mul (nativePhysicalScaleWindow_open s) hm g ε v phase (Real.exp (3*s/2))
  have hexp : Real.exp (s/2)*Real.exp (3*s/2)=Real.exp s^2 := by
    rw [←Real.exp_add,←Real.exp_nat_mul]
    congr 1
    ring
  filter_upwards [hd,hc] with x hd hc
  rw [hc] at hd
  have hh := congrArg (fun q : ℝ => Real.exp (s/2)*q) hd
  rw [←mul_assoc,hexp] at hh
  apply (mul_left_cancel₀ (pow_ne_zero 2 (Real.exp_ne_zero s)))
  nlinarith only [hh]

#print axioms nativeWeakRescaledDelaunayJacobian_const_mul
#print axioms nativeWeakPhysicalRow_identity
end Yamabe3.Analysis.SpherePolar
