import Yamabe3.Analysis.NativeC1RestrictedEnergy
import Yamabe3.Analysis.NativeChartCauchyGluing

/-! Actual completed restricted energy transported to the retained chart
metric. The pullback metric and volume density are checked pointwise. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT VectorField
open scoped Manifold ContDiff Topology RealInnerProductSpace Bundle
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
namespace Yamabe3.Analysis
open SpherePolar PoincareMT.LeviCivitaData.Dirichlet EuclideanSphereTrace
open GreenParametrix NativeChartSphereMetric
local notation "E" => EuclideanSpace ℝ (Fin 3)
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem native_chart_C1_gradient_pairing
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {x:E} (hx:x∈e.source) (hcoeff:gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    {U H:M→ℝ} (hU:MDifferentiableAt (𝓡 3) 𝓘(ℝ,ℝ) U (e x))
    (hH:MDifferentiableAt (𝓡 3) 𝓘(ℝ,ℝ) H (e x)) :
    g.inner (e x) (g.leviCivitaData.gradient U (e x)) (g.leviCivitaData.gradient H (e x))=
      gE.inner x (gE.leviCivitaData.gradient (U∘e) x) (gE.leviCivitaData.gradient (H∘e) x) := by
  have hD:e.MDifferentiable (𝓡 3) (𝓡 3):=⟨he.mdifferentiableOn (by simp),hei.mdifferentiableOn (by simp)⟩
  have hi:(mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible:=⟨hD.mfderiv hx,rfl⟩
  have hm:=ChartOperatorTransfer.metric_pairing_of_coefficients g gE e x hcoeff
  rw [gE.leviCivitaData.gradient_comp_eq_mpullback g.leviCivitaData (hD.mdifferentiableAt hx) hU hi hm,
    gE.leviCivitaData.gradient_comp_eq_mpullback g.leviCivitaData (hD.mdifferentiableAt hx) hH hi hm,hm]
  simp only [mpullback,hi.self_apply_inverse]

theorem native_C1_gradient_pairing_integral_chart
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {S:Set E} (hS:IsCompact S) (hSs:S⊆e.source)
    (hcoeff:∀x∈S,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    {U H:M→ℝ} (hU:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) 1 U) (hH:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) 1 H) :
    (∫y in e '' S,g.inner y (g.leviCivitaData.gradient U y) (g.leviCivitaData.gradient H y) ∂g.volumeMeasure)=
      ∫x in S,gE.inner x (gE.leviCivitaData.gradient (U∘e) x) (gE.leviCivitaData.gradient (H∘e) x) ∂gE.volumeMeasure := by
  rw [integral_compact_image_eq_pullback_density (g:=g) e he hei hS hSs
    (NativeC1Green.continuous_inner_gradient_C1 g.leviCivitaData hU hH).measurable]
  have hr:(∫x in S,gE.inner x (gE.leviCivitaData.gradient (U∘e) x) (gE.leviCivitaData.gradient (H∘e) x) ∂gE.volumeMeasure)=
      ∫x in S,gE.inner x (gE.leviCivitaData.gradient (U∘e) x) (gE.leviCivitaData.gradient (H∘e) x)*gE.pullbackVolumeDensity id x := by
    rw [←integral_indicator hS.measurableSet,native_integral_eq_density gE,←integral_indicator hS.measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall fun x=>by
      by_cases hx:x∈S
      · simp only [indicator_of_mem hx]
      · simp only [indicator_of_notMem hx,zero_mul]
  rw [hr]
  apply setIntegral_congr_fun hS.measurableSet
  intro x hx
  dsimp only
  rw [native_chart_C1_gradient_pairing g gE e he hei (hSs hx) (hcoeff x hx)
    (hU.mdifferentiable (by simp) _) (hH.mdifferentiable (by simp) _),
    pullbackVolumeDensity_eq_of_coefficients g gE e x (hcoeff x hx)]

variable [CompactSpace M] [ConnectedSpace M]
theorem nativeRestrictedGradientEnergy_C1_chart
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K O S:Set E} (hK:IsCompact K) (hKs:K⊆e.source) (hOK:O⊆K) (hO:IsOpen O)
    (hS:IsCompact S) (hSO:S⊆O)
    (hcoeff:∀x∈S,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (w:H1Zero g.leviCivitaData univ) {U:M→ℝ} (hU:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) 1 U)
    (hrep:(toL2 g.leviCivitaData univ w:M→ℝ)=ᵐ[g.volumeMeasure] U)
    (φ:EnergyTest g.leviCivitaData univ) :
    nativeRestrictedGradientEnergy g (e '' S) w (φ:H1Zero g.leviCivitaData univ)=
      ∫x in S,gE.inner x (gE.leviCivitaData.gradient (U∘e) x) (gE.leviCivitaData.gradient (φ∘e) x) ∂gE.volumeMeasure := by
  rw [nativeRestrictedGradientEnergy_C1_representative g e he hei hK hKs hOK hO hS hSO w hU hrep φ]
  exact native_C1_gradient_pairing_integral_chart g gE e he hei hS (hSO.trans (hOK.trans hKs)) hcoeff hU (φ.smooth.of_le (by simp))

#print axioms native_chart_C1_gradient_pairing
#print axioms native_C1_gradient_pairing_integral_chart
#print axioms nativeRestrictedGradientEnergy_C1_chart
end Yamabe3.Analysis
