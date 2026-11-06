import Yamabe3.Analysis.NativePhysicalShellPairing
import Yamabe3.Analysis.NativeDensityChartSourcePairing
import Yamabe3.Analysis.NativeChartAeTransport

/-! The actual native density-corrected source pairs with the same full
physical spectral test. Native density and the 3D scale are checked
explicitly; no projection or measure identification is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem nativeDensityCorrectedSource_actual_pairing
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (hcoeff:∀x∈K,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    {f:E→ℝ} (hf:MemLp f 2 volume) (η:EnergyTest g.leviCivitaData univ):
    (∫y,nativeDensityCorrectedChartSource gE e K f y*η y ∂g.volumeMeasure)=
      ∫x in K,f x*η (e x):=by
  let F:=hf.toLp f
  let T:=nativeDensityChartSourceCLM g gE e he hei hK hKs
  have hF:(T F:M→ℝ)=ᵐ[g.volumeMeasure]nativeDensityCorrectedChartSource gE e K f:=by
    apply (nativeDensityChartSourceCLM_ae g gE e he hei hK hKs F).trans
    exact nativeCompactChart_congr_volume_ae g e he hei hK.measurableSet
      ((ae_restrict_of_ae (s:=K) hf.coeFn_toLp).mono fun x hx=>congrArg (fun q:ℝ=>q/gE.pullbackVolumeDensity id x) hx)
  calc
    _=inner ℝ (T F) (toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ)):=by
      rw [L2.inner_def,toL2_coe]
      apply integral_congr_ae
      filter_upwards [hF,η.memLp.coeFn_toLp] with y hy hη
      simp only [Real.inner_apply]
      change _=(T F:M→ℝ) y*(η.memLp.toLp η) y
      rw [hy,hη]
    _=∫x in K,(F:E→ℝ) x*η (e x):=
      nativeDensityChartSourceCLM_pairing g gE e he hei hK hKs hcoeff F η
    _=_:=by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (s:=K) hf.coeFn_toLp] with x hx
      rw [hx]

theorem nativeDensityPhysicalShell_full_pairing
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (hcoeff:∀x∈K,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    {a:ℝ} (ha:0<a) (s:ℝ) (U:NativeCollarL2)
    (hfit:∀x:E,Real.exp (s-Real.log a) • x∈nativeSourceShell→x∈K)
    (η:EnergyTest g.leviCivitaData univ)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ)
    (htest:∀x∈K,φ (a⁻¹ • x)=η (e x)):
    (∫y,nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a s U) y*η y ∂g.volumeMeasure)=
      8*a*inner ℝ (nativeFullShellSourceReturnCLM s U) (nativePhysicalPairTestL2 φ hφ hc h0):=by
  rw [nativeDensityCorrectedSource_actual_pairing g gE e he hei hK hKs hcoeff
    (nativePhysicalShellSource_memLp_two a s U) η]
  calc
    _=∫x in K,nativePhysicalShellSource a s U x*φ (a⁻¹ • x):=by
      apply setIntegral_congr_fun hK.measurableSet
      intro x hx
      change nativePhysicalShellSource a s U x*η (e x)=nativePhysicalShellSource a s U x*φ (a⁻¹ • x)
      exact congrArg (fun q:ℝ=>nativePhysicalShellSource a s U x*q) (htest x hx).symm
    _=∫x:E,nativePhysicalShellSource a s U x*φ (a⁻¹ • x):=by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [nativePhysicalShellSource_zero_off a s U (fun hs=>hx (hfit x hs)),zero_mul]
    _=_:=nativePhysicalShellSource_full_pairing ha s U φ hφ hc h0

#print axioms nativeDensityCorrectedSource_actual_pairing
#print axioms nativeDensityPhysicalShell_full_pairing
end Yamabe3.Analysis.SpherePolar
