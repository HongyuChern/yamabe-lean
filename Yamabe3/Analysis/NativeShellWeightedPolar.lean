import Yamabe3.Analysis.NativeShellSourceReturn

/-! The inverse-square weight cancels the real log-polar Jacobian
against two cylinder lifts. All identities use Euclidean volume. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeSourceShell_subset_collar : nativeSourceShell ⊆ nativePoissonEntranceCollar := by
  intro x hx
  refine ⟨hx.1,?_⟩
  have ht := hx.2
  change -(1/2:ℝ)< -Real.log ‖x‖ ∧ -Real.log ‖x‖<(1/2:ℝ)
  constructor <;> linarith [ht.1,ht.2]

theorem nativeShellSourceWeight_cylinderPoint (p : ℝ × S) :
    nativeShellSourceWeight (cylinderPoint p)=
      (Ioc (-(1/4:ℝ)) (1/4)).indicator (fun t => Real.exp (2*t)) p.1 := by
  have hs := cylinderPoint_mem_timeWindow_iff (Ioc (-(1/4:ℝ)) (1/4)) p
  change cylinderPoint p∈nativeSourceShell ↔ p.1∈Ioc (-(1/4:ℝ)) (1/4) at hs
  by_cases ht : p.1∈Ioc (-(1/4:ℝ)) (1/4)
  · rw [nativeShellSourceWeight,indicator_of_mem (hs.mpr ht),indicator_of_mem ht]
    simp only [nativeHalfEndPotentialCoefficient,BoundedContinuousFunction.const_apply,
      cylinderPoint_norm,one_div,←Real.exp_nat_mul,←Real.exp_neg]
    congr 1
    ring
  · rw [nativeShellSourceWeight,indicator_of_notMem (fun hx => ht (hs.mp hx)),indicator_of_notMem ht]

theorem nativeShell_weighted_lifts_polar (w z : ℝ × S → ℝ) (p : ℝ × S) :
    logCylinderWeight (fun x => nativeShellSourceWeight x*cylinderLift w x*cylinderLift z x) p=
      (Ioc (-(1/4:ℝ)) (1/4)).indicator (fun t => w (t,p.2)*z (t,p.2)) p.1 := by
  change Real.exp (-3*p.1)*(nativeShellSourceWeight (cylinderPoint p)*
    cylinderLift w (Real.exp (-p.1) • (p.2:E))*cylinderLift z (Real.exp (-p.1) • (p.2:E)))=_
  rw [nativeShellSourceWeight_cylinderPoint]
  by_cases ht : p.1∈Ioc (-(1/4:ℝ)) (1/4)
  · rw [indicator_of_mem ht,indicator_of_mem ht,cylinderLift_smul w (Real.exp_pos _) p.2,
      cylinderLift_smul z (Real.exp_pos _) p.2,Real.log_exp,neg_neg,radialScale_exp_neg]
    have he : Real.exp (-3*p.1)*Real.exp (2*p.1)*Real.exp (p.1/2)*Real.exp (p.1/2)=1 := by
      rw [←Real.exp_add,←Real.exp_add,←Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    calc
      _ = (Real.exp (-3*p.1)*Real.exp (2*p.1)*Real.exp (p.1/2)*Real.exp (p.1/2))*
        (w (p.1,p.2)*z (p.1,p.2)) := by ring
      _ = _ := by rw [he,one_mul]
  · simp only [indicator_of_notMem ht,zero_mul,mul_zero]

#print axioms nativeSourceShell_subset_collar
#print axioms nativeShellSourceWeight_cylinderPoint
#print axioms nativeShell_weighted_lifts_polar
end Yamabe3.Analysis.SpherePolar
