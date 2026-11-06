import Yamabe3.Analysis.NativeDensityChartL2Operator
import Yamabe3.Analysis.NativePhysicalShellSourceCLM

/-! Explicit linearity and a.e. transport for the actual density-
corrected native source. This permits comparing raw source formulas
without confusing pointwise representatives with their L2 classes. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

 theorem nativeDensitySource_congr_volume_ae
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:MeasurableSet K) {f h:E→ℝ} (hfh:f=ᵐ[volume]h):
    nativeDensityCorrectedChartSource gE e K f=ᵐ[g.volumeMeasure]nativeDensityCorrectedChartSource gE e K h:=by
  apply nativeCompactChart_congr_volume_ae g e he hei hK
  filter_upwards [ae_restrict_of_ae (s:=K) hfh] with x hx
  rw [hx]

 theorem nativeDensitySource_add
    (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M) (K:Set E) (f h:E→ℝ):
    nativeDensityCorrectedChartSource gE e K (f+h)=
      nativeDensityCorrectedChartSource gE e K f+nativeDensityCorrectedChartSource gE e K h:=by
  have he:(fun x:E=>(f+h) x/gE.pullbackVolumeDensity id x)=
      (fun x:E=>f x/gE.pullbackVolumeDensity id x)+(fun x:E=>h x/gE.pullbackVolumeDensity id x):=by
    funext x
    simp only [Pi.add_apply,add_div]
  unfold nativeDensityCorrectedChartSource
  rw [he]
  exact (nativeCompactChartFunctionLinear e K).map_add _ _

 theorem nativeDensityPhysicalShell_add_ae
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:MeasurableSet K) (a s:ℝ) (U W:NativeCollarL2):
    nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a s (U+W))=ᵐ[g.volumeMeasure]
      (nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a s U)+
        nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a s W)):=by
  have hh:=nativeDensitySource_congr_volume_ae g gE e he hei hK (nativePhysicalShellSource_add_ae a s U W)
  rw [nativeDensitySource_add] at hh
  exact hh

#print axioms nativeDensitySource_congr_volume_ae
#print axioms nativeDensitySource_add
#print axioms nativeDensityPhysicalShell_add_ae
end Yamabe3.Analysis.SpherePolar
