import Yamabe3.Analysis.NativeDensityChartL2Operator
import Yamabe3.Analysis.NativeCompactChartSource
import Yamabe3.Analysis.Green.NativeChartOperatorTransfer
import Yamabe3.Analysis.NativeChartSphereMetric

/-! The actual density-corrected L2 source, with its native test pairing.
The density cancels because actual chart coefficients agree, not because
the coordinate and native measures are silently identified. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
open GreenParametrix ChartOperatorTransfer NativeChartSphereMetric
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

def nativeDensityChartSourceCLM
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source) :
    Lp ℝ 2 (volume:Measure E) →L[ℝ] Lp ℝ 2 g.volumeMeasure :=
  (exists_nativeDensityCorrectedChartL2_CLM g gE e he hei hK hKs).choose_spec.choose

theorem nativeDensityChartSourceCLM_ae
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source) (F:Lp ℝ 2 (volume:Measure E)) :
    (nativeDensityChartSourceCLM g gE e he hei hK hKs F:M→ℝ)=ᵐ[g.volumeMeasure]
      nativeDensityCorrectedChartSource gE e K (F:E→ℝ) :=
  (exists_nativeDensityCorrectedChartL2_CLM g gE e he hei hK hKs).choose_spec.choose_spec.2.2 F

theorem nativeDensityChartSourceCLM_pairing
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (hcoeff:∀x∈K,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (F:Lp ℝ 2 (volume:Measure E)) (φ:EnergyTest g.leviCivitaData univ) :
    inner ℝ (nativeDensityChartSourceCLM g gE e he hei hK hKs F)
      (toL2 g.leviCivitaData univ (φ:H1Zero g.leviCivitaData univ))=
      ∫x in K,(F:E→ℝ) x*φ (e x) := by
  rw [L2.inner_def,toL2_coe]
  trans ∫y,nativeCompactChartFunction e K (fun x=>(F:E→ℝ) x/gE.pullbackVolumeDensity id x) y*φ y ∂g.volumeMeasure
  · apply integral_congr_ae
    filter_upwards [nativeDensityChartSourceCLM_ae g gE e he hei hK hKs F,φ.memLp.coeFn_toLp] with y hy hφ
    simp only [Real.inner_apply,hy]
    change nativeDensityCorrectedChartSource gE e K (F:E→ℝ) y*(φ.memLp.toLp φ) y=_
    rw [hφ]
    rfl
  · refine (integral_nativeCompactChartFunction_mul g e he hei hK hKs
        (f:=fun x=>(F:E→ℝ) x/gE.pullbackVolumeDensity id x) (φ:=(φ:M→ℝ))
        ((Lp.stronglyMeasurable F).measurable.div (native_density_smooth_positive gE).1.continuous.measurable)
        φ.smooth.continuous.measurable).trans ?_
    apply setIntegral_congr_fun hK.measurableSet
    intro x hx
    dsimp only
    rw [←pullbackVolumeDensity_eq_of_coefficients g gE e x (hcoeff x hx)]
    field_simp [(native_density_smooth_positive gE).2 x |>.ne']

#print axioms nativeDensityChartSourceCLM_ae
#print axioms nativeDensityChartSourceCLM_pairing
end Yamabe3.Analysis.SpherePolar
