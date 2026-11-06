import Yamabe3.Analysis.NativeBCFPhysicalShellSource
import Yamabe3.Analysis.NativePhysicalShellPairing

/-! A closed full BCF shell's spectral pairing is the integral of the
actual weak native operator of the SAME physical field, on the literal
half-open shell. This is a proved operator identity, not a norm surrogate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay SphereSpectrum

 theorem nativeBCF_same_field_shell_pairing (g:RiemannianMetric 3 E) (a s:ℝ) (V:ℝ→ᵇℝ)
    (J:nativeCollarJetClosure) {u:E→ℝ}
    (hJ:(J.val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun y=>Real.exp (3*s/2)*u (Real.exp (-s) • y)))
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ):
    inner ℝ (nativeFullShellSourceReturnCLM s
      (nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s V) J.val+
        nativeBCFCollarErrorCLM g (a*Real.exp (-s)) (boundedTimeTranslate ℝ s V) J.val))
      (nativePhysicalPairTestL2 φ hφ hc h0)=
      ∫x in nativeScaledSourceShell s,(nativeWeakRescaledDelaunayJacobian (nativePhysicalScaleWindow s) g a (fun _=>0) 0 u x-
        g.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*u x)*φ x:=by
  let U:NativeCollarL2:=nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s V) J.val+
    nativeBCFCollarErrorCLM g (a*Real.exp (-s)) (boundedTimeTranslate ℝ s V) J.val
  have he:=nativeBCF_shell_actual_weak_source g a s V J hJ
  have hp:=nativePhysicalShellSource_full_pairing (a:=1) (by norm_num) s U φ hφ hc h0
  simp only [inv_one,one_smul,mul_one] at hp
  have hh:(∫x:E,nativePhysicalShellSource 1 s U x*φ x)=
      8*(∫x in nativeScaledSourceShell s,(nativeWeakRescaledDelaunayJacobian (nativePhysicalScaleWindow s) g a (fun _=>0) 0 u x-
        g.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*u x)*φ x):=by
    rw [←integral_const_mul,←integral_indicator (nativeScaledSourceShell_measurable s)]
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
    by_cases hxs:x∈nativeScaledSourceShell s
    · simp only [indicator_of_mem hxs]
      ring
    · simp only [indicator_of_notMem hxs,mul_zero,zero_mul]
  exact (mul_left_cancel₀ (by norm_num:(8:ℝ)≠0) (hp.symm.trans hh))

#print axioms nativeBCF_same_field_shell_pairing
end Yamabe3.Analysis.SpherePolar
