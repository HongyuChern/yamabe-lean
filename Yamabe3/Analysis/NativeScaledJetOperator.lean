import Yamabe3.Analysis.NativeTwoSidedDelaunayBinding

/-! Actual scaled weak operators for an arbitrary true collar jet with
one physical representative. All a.e. identities are transported by the
nonzero dilation measure map. The flat operator is treated separately
from the native operator, retaining the same potential and weights. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

theorem nativeScaledJet_physical_operator (g : RiemannianMetric 3 E) (ε : ℝ)
    (v : ℝ→ℝ) (hv : ContDiff ℝ ∞ v) (hb : ∀t,0≤v t ∧ v t≤1)
    (phase s : ℝ) (J : nativeCollarJetClosure) {u : E→ℝ}
    (he : (J.val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • x))) :
    (fun x => Real.exp (s/2)*(nativeOrbitCollarJacobianCLM g (ε*Real.exp (-s)) v hv hb (phase+s) J.val : E→ℝ)
      (Real.exp s • x))=ᵐ[volume.restrict (nativePhysicalScaleWindow s)]
      nativeWeakRescaledDelaunayJacobian (nativePhysicalScaleWindow s) g ε v phase u := by
  have hw := nativeOrbitCollarJacobian_weak_ae g (ε*Real.exp (-s)) v hv hb (phase+s) J
  have hc := nativeWeakRescaledDelaunayJacobian_congr (nativePolarTimeWindow_open (1/2)) g (ε*Real.exp (-s)) v (phase+s) he
  have hd := ae_comp_dilation (Real.exp_ne_zero s) (hw.trans hc)
  have hu := (MemWkp_congr_ae (by norm_num) (nativePolarTimeWindow_open (1/2)) he).mp (nativeCollarJetClosure_memH2 J)
  have hp := nativeWeakPhysicalRow_identity g ε v phase s hu
  filter_upwards [hd,hp] with x hd hp
  exact (congrArg (fun z : ℝ => Real.exp (s/2)*z) hd).trans hp

theorem nativeWeakLaplacian_scaled_back (s : ℝ) {u : E→ℝ}
    (hu : MemWkp 2 2 (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • x)) nativePoissonEntranceCollar) :
    (fun x => Real.exp (s/2)*weakNegativeLaplacian nativePoissonEntranceCollar
      (fun y => Real.exp (3*s/2)*u (Real.exp (-s) • y)) (Real.exp s • x))
      =ᵐ[volume.restrict (nativePhysicalScaleWindow s)] weakNegativeLaplacian (nativePhysicalScaleWindow s) u := by
  have hd := weakNegativeLaplacian_comp_dilation (Real.exp_ne_zero s) (nativePolarTimeWindow_open (1/2)) hu
  have hfun : (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • (Real.exp s • x)))=
      (fun x => Real.exp (3*s/2)*u x) := by
    funext x
    rw [smul_smul,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_smul]
  rw [hfun] at hd
  change weakNegativeLaplacian (nativePhysicalScaleWindow s) (fun x => Real.exp (3*s/2)*u x)
      =ᵐ[volume.restrict (nativePhysicalScaleWindow s)]
      (fun x => Real.exp s^2*weakNegativeLaplacian nativePoissonEntranceCollar
        (fun y => Real.exp (3*s/2)*u (Real.exp (-s) • y)) (Real.exp s • x)) at hd
  have hc := weakNegativeLaplacian_const_mul (nativePhysicalScaleWindow_open s)
    (native_scaled_H2_to_physical s hu) (Real.exp (3*s/2))
  have hexp : Real.exp (s/2)*Real.exp (3*s/2)=Real.exp s^2 := by
    rw [←Real.exp_add,←Real.exp_nat_mul]
    congr 1
    ring
  filter_upwards [hd,hc] with x hd hc
  rw [hc] at hd
  have hh := congrArg (fun z : ℝ => Real.exp (s/2)*z) hd
  rw [←mul_assoc,hexp] at hh
  apply mul_left_cancel₀ (pow_ne_zero 2 (Real.exp_ne_zero s))
  nlinarith only [hh]

theorem nativeScaledJet_flat_physical_operator (v : ℝ→ℝ) (hv : Continuous v)
    (hb : ∀t,0≤v t ∧ v t≤1) (phase s : ℝ) (J : nativeCollarJetClosure) {u : E→ℝ}
    (he : (J.val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • x))) :
    (fun x => Real.exp (s/2)*(nativeFlatCollarJetCLM (delaunayPhasePotentialBCF v hv hb (phase+s)) J.val : E→ℝ)
      (Real.exp s • x))=ᵐ[volume.restrict (nativePhysicalScaleWindow s)]
      (fun x => weakNegativeLaplacian (nativePhysicalScaleWindow s) u x+annularDelaunayPotential v phase x*u x) := by
  let V := delaunayPhasePotentialBCF v hv hb (phase+s)
  have hQ (x : E) : nativeHalfEndPotentialCoefficient V x= -annularDelaunayPotential v (phase+s) x := by
    change (15/4)*v (-Real.log ‖x‖+(phase+s))^4/‖x‖^2= -(-(15/4)*v (phase+s-Real.log ‖x‖)^4/‖x‖^2)
    rw [show -Real.log ‖x‖+(phase+s)=phase+s-Real.log ‖x‖ by ring]
    ring
  have hu := (MemWkp_congr_ae (by norm_num) (nativePolarTimeWindow_open (1/2)) he).mp (nativeCollarJetClosure_memH2 J)
  have hl := weakNegativeLaplacian_congr_ae (nativePolarTimeWindow_open (1/2)) he
  have hf := nativeFlatCollarJet_weak_ae V J
  have hrow : (nativeFlatCollarJetCLM V J.val : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => weakNegativeLaplacian nativePoissonEntranceCollar
        (fun y => Real.exp (3*s/2)*u (Real.exp (-s) • y)) x+
        annularDelaunayPotential v (phase+s) x*(Real.exp (3*s/2)*u (Real.exp (-s) • x))) := by
    filter_upwards [hf,hl,he] with x hf hl he
    change weakNegativeLaplacian nativePoissonEntranceCollar J.val.1 x=weakNegativeLaplacian nativePoissonEntranceCollar
      (fun y => Real.exp (3*s/2)*u (Real.exp (-s) • y)) x at hl
    rw [hf,hl,he,hQ]
    ring
  have hd := ae_comp_dilation (Real.exp_ne_zero s) hrow
  have hback := nativeWeakLaplacian_scaled_back s hu
  have hfun (x : E) : Real.exp (-s) • (Real.exp s • x)=x := by
    rw [smul_smul,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_smul]
  filter_upwards [hd,hback,ae_restrict_mem (nativePhysicalScaleWindow_open s).measurableSet] with x hd hback hx
  have hx0 : x≠0 := by
    intro heq
    have hx' : Real.exp s • x∈nativePoissonEntranceCollar := hx
    have hn := hx'.1
    exact hn (by simp only [heq,smul_zero,mem_singleton_iff])
  have hpot : Real.exp s^2*annularDelaunayPotential v (phase+s) (Real.exp s • x)=annularDelaunayPotential v phase x := by
    unfold annularDelaunayPotential
    rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos s).le,
      Real.log_mul (Real.exp_ne_zero s) (norm_ne_zero_iff.mpr hx0),Real.log_exp]
    rw [show phase+s-(s+Real.log ‖x‖)=phase-Real.log ‖x‖ by ring]
    field_simp [Real.exp_ne_zero s,norm_ne_zero_iff.mpr hx0]
    <;> ring
  have hexp : Real.exp (s/2)*Real.exp (3*s/2)=Real.exp s^2 := by
    rw [←Real.exp_add,←Real.exp_nat_mul]
    congr 1
    ring
  rw [hd,mul_add,hback,hfun]
  congr 1
  calc
    _=(Real.exp (s/2)*Real.exp (3*s/2))*annularDelaunayPotential v (phase+s) (Real.exp s • x)*u x := by ring
    _=_ := by rw [hexp,hpot]

#print axioms nativeScaledJet_physical_operator
#print axioms nativeWeakLaplacian_scaled_back
#print axioms nativeScaledJet_flat_physical_operator
end Yamabe3.Analysis.SpherePolar
