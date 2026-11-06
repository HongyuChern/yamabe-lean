import Yamabe3.Analysis.NativePhysicalShellCriticalTransport
import Yamabe3.Analysis.NativePhysicalPairTestScaling

/-! The physical shell source and the full spectral test have EXACTLY
the same pairing, with factor 8a in dimension three. All angular modes
and the actual physical source representative are retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay

theorem nativePhysicalShellSource_full_pairing
    {a:ℝ} (ha:0<a) (s:ℝ) (U:NativeCollarL2)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ):
    (∫x:E,nativePhysicalShellSource a s U x*φ (a⁻¹ • x))=
      8*a*inner ℝ (nativeFullShellSourceReturnCLM s U) (nativePhysicalPairTestL2 φ hφ hc h0):=by
  rw [nativeFullShellSourceReturn_physical_test φ hφ hc h0 s U]
  have hmul(x:E):Real.exp (-s) • (Real.exp (s-Real.log a) • x)=a⁻¹ • x:=by
    rw [smul_smul,←Real.exp_add,show -s+(s-Real.log a)= -Real.log a by ring,Real.exp_neg,Real.exp_log ha]
  have he:(fun x:E=>nativePhysicalShellSource a s U x*φ (a⁻¹ • x))=
      (fun x:E=>(8*Real.exp (-2*Real.log a+s/2))*
        ((nativeZeroShellSource U (Real.exp (s-Real.log a) • x))*
          φ (Real.exp (-s) • (Real.exp (s-Real.log a) • x)))):=by
    funext x
    rw [hmul]
    dsimp only [nativePhysicalShellSource]
    ring
  rw [he,integral_const_mul]
  have hd:=setIntegral_comp_dilation (Real.exp_ne_zero (s-Real.log a)) (univ:Set E)
    (fun y:E=>nativeZeroShellSource U y*φ (Real.exp (-s) • y))
  simp only [preimage_univ,Measure.restrict_univ,finrank_euclideanSpace_fin,
    ←Real.exp_nat_mul,abs_of_pos (Real.exp_pos _),←Real.exp_neg] at hd
  rw [hd]
  have hi:(∫x:E,nativeZeroShellSource U x*φ (Real.exp (-s) • x))=
      ∫x in nativeSourceShell,(U:E→ℝ) x*φ (Real.exp (-s) • x):=by
    rw [←integral_indicator nativeSourceShell_measurable]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx:x∈nativeSourceShell
    · simp only [nativeZeroShellSource,indicator_of_mem hx]
    · simp only [nativeZeroShellSource,indicator_of_notMem hx,zero_mul]
  rw [hi]
  have hc0:Real.exp (-2*Real.log a+s/2)*Real.exp (-(3*(s-Real.log a)))=
      a*Real.exp (-5*s/2):=by
    rw [←Real.exp_add]
    calc
      _=Real.exp (Real.log a)*Real.exp (-5*s/2):=by
        rw [←Real.exp_add]
        congr 1
        ring
      _=_:=by rw [Real.exp_log ha]
  calc
    _=8*(Real.exp (-2*Real.log a+s/2)*Real.exp (-(3*(s-Real.log a))))*
      (∫x in nativeSourceShell,(U:E→ℝ) x*φ (Real.exp (-s) • x)):=by ring
    _=_:=by rw [hc0];ring

#print axioms nativePhysicalShellSource_full_pairing
end Yamabe3.Analysis.SpherePolar
