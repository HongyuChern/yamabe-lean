import Yamabe3.Analysis.NativeExteriorGeometricResidual
import Yamabe3.Analysis.NativeWeakPhysicalRow
import Yamabe3.Analysis.NativeWeakDivergenceJacobian

/-! The full flat-plus-geometric BCF row is the SAME field's actual
weak native operator minus its physical potential. Exact dilation keeps
scalar curvature, density, source normalization and all weak derivatives. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

 theorem nativeWeakZeroJacobian_phase (O:Set E) (g:RiemannianMetric 3 E) (r t:ℝ) (u:E→ℝ):
    nativeWeakRescaledDelaunayJacobian O g r (fun _=>0) t u=
      nativeWeakRescaledDelaunayJacobian O g r (fun _=>0) 0 u:=by
  funext x
  simp only [nativeWeakRescaledDelaunayJacobian,nativeDelaunayPotentialError,annularDelaunayPotential,zero_pow,zero_mul,mul_zero,zero_div]

 theorem nativeBCF_full_row_weak_ae (g:RiemannianMetric 3 E) (r:ℝ) (V:ℝ→ᵇℝ)
    (J:nativeCollarJetClosure):
    ((nativeFlatCollarJetCLM V J.val+nativeBCFCollarErrorCLM g r V J.val:NativeCollarL2):E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x=>nativeWeakRescaledDelaunayJacobian nativePoissonEntranceCollar g r (fun _=>0) 0 J.val.1 x-
        g.pullbackVolumeDensity id (r • x)*nativeHalfEndPotentialCoefficient V x*J.val.1 x):=by
  filter_upwards [Lp.coeFn_add (nativeFlatCollarJetCLM V J.val) (nativeBCFCollarErrorCLM g r V J.val),
    nativeFlatCollarJet_weak_ae V J,nativeBCFCollarError_weak_ae g r V J] with x ha hf hg
  change (nativeFlatCollarJetCLM V J.val+nativeBCFCollarErrorCLM g r V J.val:NativeCollarL2) x=_
  rw [ha]
  change nativeFlatCollarJetCLM V J.val x+nativeBCFCollarErrorCLM g r V J.val x=_
  rw [hf,hg]
  simp only [nativeWeakRescaledDelaunayJacobian,nativeDelaunayPotentialError,annularDelaunayPotential,
    nativeBCFPotentialError,zero_pow,zero_mul,mul_zero,zero_div]
  ring

 theorem nativeHalfEndPotentialCoefficient_translate_scale (V:ℝ→ᵇℝ) (s:ℝ) {x:E} (hx:x≠0):
    Real.exp s^2*nativeHalfEndPotentialCoefficient (boundedTimeTranslate ℝ s V) (Real.exp s • x)=
      nativeHalfEndPotentialCoefficient V x:=by
  simp only [nativeHalfEndPotentialCoefficient,norm_smul,
    Real.norm_of_nonneg (Real.exp_pos _).le,Real.log_mul (Real.exp_ne_zero s) (norm_ne_zero_iff.mpr hx),Real.log_exp]
  change Real.exp s^2*(V (-(s+Real.log ‖x‖)+s)/(Real.exp s*‖x‖)^2)=V (-Real.log ‖x‖)/‖x‖^2
  rw [show -(s+Real.log ‖x‖)+s= -Real.log ‖x‖ by ring]
  field_simp [Real.exp_ne_zero s,norm_ne_zero_iff.mpr hx]
  <;>ring

 theorem nativeBCF_same_field_physical_row (g:RiemannianMetric 3 E) (a s:ℝ) (V:ℝ→ᵇℝ)
    (J:nativeCollarJetClosure) {u:E→ℝ}
    (hJ:(J.val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun y=>Real.exp (3*s/2)*u (Real.exp (-s) • y))):
    (fun x=>Real.exp (s/2)*(nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s V) J.val+
        nativeBCFCollarErrorCLM g (a*Real.exp (-s)) (boundedTimeTranslate ℝ s V) J.val:NativeCollarL2) (Real.exp s • x))
      =ᵐ[volume.restrict (nativePhysicalScaleWindow s)]
      (fun x=>nativeWeakRescaledDelaunayJacobian (nativePhysicalScaleWindow s) g a (fun _=>0) 0 u x-
        g.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*u x):=by
  have hu:MemWkp 2 2 (fun y=>Real.exp (3*s/2)*u (Real.exp (-s) • y)) nativePoissonEntranceCollar:=
    (MemWkp_congr_ae (by norm_num) (nativePolarTimeWindow_open (1/2)) hJ).mp (nativeCollarJetClosure_memH2 J)
  have hjac:=nativeWeakRescaledDelaunayJacobian_congr (nativePolarTimeWindow_open (1/2)) g
    (a*Real.exp (-s)) (fun _=>0) 0 hJ
  have hr:=nativeBCF_full_row_weak_ae g (a*Real.exp (-s)) (boundedTimeTranslate ℝ s V) J
  have hd:=nativeWeakPhysicalRow_identity g a (fun _=>0) 0 s hu
  rw [nativeWeakZeroJacobian_phase nativePoissonEntranceCollar g (a*Real.exp (-s)) (0+s)] at hd
  have hr':=ae_comp_dilation (Real.exp_ne_zero s) hr
  have hjac':=ae_comp_dilation (Real.exp_ne_zero s) hjac
  have hJ':=ae_comp_dilation (Real.exp_ne_zero s) hJ
  filter_upwards [hr',hjac',hJ',hd,ae_restrict_mem (nativePhysicalScaleWindow_open s).measurableSet] with x hr hj hv hd hx
  have hx0:x≠0:=nativePhysicalScaleWindow_off_zero s hx
  have hm:(a*Real.exp (-s)) • (Real.exp s • x)=a • x:=by
    rw [smul_smul,mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
  have hu0:Real.exp (-s) • (Real.exp s • x)=x:=by
    rw [smul_smul,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_smul]
  change nativeWeakRescaledDelaunayJacobian nativePoissonEntranceCollar g (a*Real.exp (-s)) (fun _=>0) 0 J.val.1 (Real.exp s • x)=
    nativeWeakRescaledDelaunayJacobian nativePoissonEntranceCollar g (a*Real.exp (-s)) (fun _=>0) 0
      (fun y=>Real.exp (3*s/2)*u (Real.exp (-s) • y)) (Real.exp s • x) at hj
  rw [hr,hj,hv,hm,hu0,mul_sub,hd]
  have he:Real.exp (s/2)*Real.exp (3*s/2)=Real.exp s^2:=by
    rw [←Real.exp_add,←Real.exp_nat_mul]
    congr 1
    ring
  have hq:=nativeHalfEndPotentialCoefficient_translate_scale V s hx0
  congr 1
  calc
    _=g.pullbackVolumeDensity id (a • x)*(Real.exp s^2*
        nativeHalfEndPotentialCoefficient (boundedTimeTranslate ℝ s V) (Real.exp s • x))*u x:=by rw [←he];ring
    _=_:=by rw [hq]

#print axioms nativeWeakZeroJacobian_phase
#print axioms nativeBCF_full_row_weak_ae
#print axioms nativeHalfEndPotentialCoefficient_translate_scale
#print axioms nativeBCF_same_field_physical_row
end Yamabe3.Analysis.SpherePolar
