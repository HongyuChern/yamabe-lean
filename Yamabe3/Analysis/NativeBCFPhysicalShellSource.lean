import Yamabe3.Analysis.NativeBCFWeakPhysicalRow
import Yamabe3.Analysis.NativePhysicalShellCriticalTransport
import Yamabe3.Analysis.PhysicalOuterWindowGeometry

/-! A true closed full BCF jet produces the SAME field's native weak
operator on its literal physical shell, with factor8 and all modes.
The resulting shell operator source is actually L2, not an input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay

 theorem nativeBCF_shell_actual_weak_source (g:RiemannianMetric 3 E) (a s:ℝ) (V:ℝ→ᵇℝ)
    (J:nativeCollarJetClosure) {u:E→ℝ}
    (hJ:(J.val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun y=>Real.exp (3*s/2)*u (Real.exp (-s) • y))):
    nativePhysicalShellSource 1 s (nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s V) J.val+
        nativeBCFCollarErrorCLM g (a*Real.exp (-s)) (boundedTimeTranslate ℝ s V) J.val)
      =ᵐ[volume]
      (fun x=>8*(nativeScaledSourceShell s).indicator
        (fun x=>nativeWeakRescaledDelaunayJacobian (nativePhysicalScaleWindow s) g a (fun _=>0) 0 u x-
          g.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*u x) x):=by
  let U:NativeCollarL2:=nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s V) J.val+
    nativeBCFCollarErrorCLM g (a*Real.exp (-s)) (boundedTimeTranslate ℝ s V) J.val
  have hsub:nativeScaledSourceShell s⊆nativePhysicalScaleWindow s:=
    preimage_mono nativeSourceShell_subset_collar
  have hr:=ae_mono (Measure.restrict_mono hsub le_rfl) (nativeBCF_same_field_physical_row g a s V J hJ)
  have hh:=(ae_restrict_iff' (nativeScaledSourceShell_measurable s)).mp hr
  filter_upwards [hh] with x hx
  by_cases hxD:x∈nativeScaledSourceShell s
  · have hxs:Real.exp s • x∈nativeSourceShell:=hxD
    change nativePhysicalShellSource 1 s U x=_
    simp only [nativePhysicalShellSource,Real.log_one,mul_zero,neg_zero,sub_zero,zero_add,
      nativeZeroShellSource,indicator_of_mem hxs,indicator_of_mem hxD]
    calc
      _=8*(Real.exp (s/2)*(U:E→ℝ) (Real.exp s • x)):=by ring
      _=_:=by rw [hx hxD]
  · have hxs:Real.exp s • x∉nativeSourceShell:=hxD
    change nativePhysicalShellSource 1 s U x=_
    simp only [nativePhysicalShellSource,Real.log_one,mul_zero,neg_zero,sub_zero,zero_add,
      nativeZeroShellSource,indicator_of_notMem hxs,indicator_of_notMem hxD,mul_zero]

 theorem nativeBCF_shell_actual_weak_source_memLp (g:RiemannianMetric 3 E) (a s:ℝ) (V:ℝ→ᵇℝ)
    (J:nativeCollarJetClosure) {u:E→ℝ}
    (hJ:(J.val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun y=>Real.exp (3*s/2)*u (Real.exp (-s) • y))):
    MemLp ((nativeScaledSourceShell s).indicator
      (fun x=>nativeWeakRescaledDelaunayJacobian (nativePhysicalScaleWindow s) g a (fun _=>0) 0 u x-
        g.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*u x)) 2 volume:=by
  have he:=nativeBCF_shell_actual_weak_source g a s V J hJ
  have hm:=(nativePhysicalShellSource_memLp_two 1 s
    (nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s V) J.val+
      nativeBCFCollarErrorCLM g (a*Real.exp (-s)) (boundedTimeTranslate ℝ s V) J.val)).const_mul (1/8:ℝ)
  apply hm.ae_eq
  filter_upwards [he] with x hx
  rw [hx]
  ring

#print axioms nativeBCF_shell_actual_weak_source
#print axioms nativeBCF_shell_actual_weak_source_memLp
end Yamabe3.Analysis.SpherePolar
