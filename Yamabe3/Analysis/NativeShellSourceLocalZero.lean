import Yamabe3.Analysis.NativePhysicalShellSourceCLM
import Yamabe3.Analysis.NativeRestrictedChartAeTransport

/-! Local zero source transport is a VOLUME-a.e. statement; no boundary
restriction occurs. Shell indicators, density and the actual chart persist. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
attribute [local instance] Classical.propDecidable

theorem nativeZeroShellSource_congr_function (U:NativeCollarL2) (f:E→ℝ)
    (hf:(U:E→ℝ)=ᵐ[volume.restrict nativeSourceShell]f):
    nativeZeroShellSource U=ᵐ[volume]nativeSourceShell.indicator f:=by
  filter_upwards [(ae_restrict_iff' nativeSourceShell_measurable).mp hf] with x hx
  by_cases hs:x∈nativeSourceShell
  · simp only [nativeZeroShellSource,indicator_of_mem hs,hx hs]
  · simp only [nativeZeroShellSource,indicator_of_notMem hs]

theorem nativePhysicalShellSource_local_zero
    (a s:ℝ) (U:NativeCollarL2) (f:E→ℝ)
    (hf:(U:E→ℝ)=ᵐ[volume.restrict nativeSourceShell]f)
    {D:Set E} (hD:MeasurableSet D)
    (hz:∀x∈D,Real.exp (s-Real.log a) • x∈nativeSourceShell→f (Real.exp (s-Real.log a) • x)=0):
    nativePhysicalShellSource a s U=ᵐ[volume.restrict D](fun _=>0):=by
  have hd:=ae_comp_dilation (Real.exp_ne_zero (s-Real.log a))
    (ae_restrict_of_ae (s:=univ) (nativeZeroShellSource_congr_function U f hf))
  simp only [preimage_univ,Measure.restrict_univ] at hd
  filter_upwards [ae_restrict_of_ae (s:=D) hd,ae_restrict_mem hD] with x hx hxD
  dsimp only [nativePhysicalShellSource]
  rw [hx]
  by_cases hs:Real.exp (s-Real.log a) • x∈nativeSourceShell
  · rw [indicator_of_mem hs,hz x hxD hs,mul_zero]
  · rw [indicator_of_notMem hs,mul_zero]

variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem nativeDensityCorrectedChartSource_local_zero
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K D:Set E} (hKs:K⊆e.source) (hD:IsOpen D) (hDK:D⊆K)
    (f:E→ℝ) (hf:f=ᵐ[volume.restrict D](fun _=>0)):
    nativeDensityCorrectedChartSource gE e K f=ᵐ[g.volumeMeasure.restrict (e '' D)](fun _=>0):=by
  have hCoord:K.indicator (fun x=>f x/gE.pullbackVolumeDensity id x)=ᵐ[volume.restrict D](fun _=>0):=by
    filter_upwards [hf,ae_restrict_mem hD.measurableSet] with x hx hxD
    rw [indicator_of_mem (hDK hxD),hx,zero_div]
  have hn:=coordinateExtension_congr_restricted_volume_ae g e he hei hD (hDK.trans hKs) hCoord
  have hZero:coordinateExtension e (fun _:E=>0)=(fun _:M=>0):=by
    funext y
    simp only [coordinateExtension,indicator_zero,Function.comp_def,Pi.zero_apply]
  simpa only [nativeDensityCorrectedChartSource,nativeCompactChartFunction,hZero] using hn

#print axioms nativeZeroShellSource_congr_function
#print axioms nativePhysicalShellSource_local_zero
#print axioms nativeDensityCorrectedChartSource_local_zero
end Yamabe3.Analysis.SpherePolar
