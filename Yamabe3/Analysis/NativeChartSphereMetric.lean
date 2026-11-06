import GreenMass.NativeGaussSphereArea
import PoincareLib.Geometry.Riemannian.Coordinates.Coefficients
import PoincareLib.Geometry.Riemannian.Connection.Euclidean

/-!
# The actual manifold sphere metric in the retained coordinate chart

The sphere map is the literal composition of the retained chart with radius
dilation. Smoothness and immersion are proved from the actual chart and its
inverse. Its induced metric is identified with the retained extended metric
using the actual coefficient identity. Consequently the proved area formula
uses the original manifold metric's pullback volume density.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle ENNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace Yamabe3.Analysis.NativeChartSphereMetric

open GreenMass.NativeSphereGeometry GreenMass.NativeSphereDilation
  GreenMass.NativeGaussSphereArea

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- Smoothness of the actual chart sphere map, with its whole image in the
true chart source. -/
theorem smooth_chartRadiusMap
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (r : ℝ) (hs : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source) :
    ContMDiff (𝓡 2) (𝓡 3) ∞ (e ∘ GreenMass.SphereMeasure.dilation r) :=
  he.comp_contMDiff (smooth_dilation r) hs

/-- The chart sphere is an immersion because both its actual differential
factors are injective. -/
theorem immersion_chartRadiusMap
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (r : ℝ) (hr : r ≠ 0)
    (hs : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source)
    (θ : S) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3)
      (e ∘ GreenMass.SphereMeasure.dilation r) θ) := by
  have hD : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  rw [mfderiv_comp θ
    ((he.contMDiffAt (e.open_source.mem_nhds (hs θ))).mdifferentiableAt (by simp))
    ((smooth_dilation r).mdifferentiable (by simp) θ)]
  exact (hD.mfderiv_injective (hs θ)).comp (immersion_dilation r hr θ)

/-- The metric induced from the original manifold metric by the actual
sphere parametrization. -/
def chartRadiusMetric (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (r : ℝ) (hr : r ≠ 0)
    (hs : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source) :
    RiemannianMetric 2 S :=
  RiemannianMetric.Induced.pullbackMetric g
    (e ∘ GreenMass.SphereMeasure.dilation r)
    (smooth_chartRadiusMap e he r hs) (immersion_chartRadiusMap e he hei r hr hs)

/-- Pointwise equality of the actual sphere differential pairings follows
from the given identity of the actual ambient coefficient fields. -/
theorem chartRadiusMetric_inner_eq_gaussRadiusMetric
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (r : ℝ) (hr : r ≠ 0)
    (hs : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source)
    (θ : S) (v w : TangentSpace (𝓡 2) θ)
    (hcoeff : gE.euclideanCoefficients (GreenMass.SphereMeasure.dilation r θ) =
      g.pullbackCoefficients e (GreenMass.SphereMeasure.dilation r θ)) :
    (chartRadiusMetric g e he hei r hr hs).inner θ v w =
      (gaussRadiusMetric gE r hr).inner θ v w := by
  change g.inner (e (GreenMass.SphereMeasure.dilation r θ))
    (mfderiv (𝓡 2) (𝓡 3) (e ∘ GreenMass.SphereMeasure.dilation r) θ v)
    (mfderiv (𝓡 2) (𝓡 3) (e ∘ GreenMass.SphereMeasure.dilation r) θ w) = _
  rw [mfderiv_comp θ
    ((he.contMDiffAt (e.open_source.mem_nhds (hs θ))).mdifferentiableAt (by simp))
    ((smooth_dilation r).mdifferentiable (by simp) θ)]
  change g.pullbackCoefficients e (GreenMass.SphereMeasure.dilation r θ)
    (mfderiv (𝓡 2) (𝓡 3) (GreenMass.SphereMeasure.dilation r) θ v)
    (mfderiv (𝓡 2) (𝓡 3) (GreenMass.SphereMeasure.dilation r) θ w) = _
  rw [← hcoeff]
  rfl

private theorem metric_eq_of_inner_eq {g₁ g₂ : RiemannianMetric 2 S}
    (h : g₁.inner = g₂.inner) : g₁ = g₂ := by
  cases g₁
  cases g₂
  cases h
  rfl

/-- Equality of genuine induced metrics, not just a free measure comparison. -/
theorem chartRadiusMetric_eq_gaussRadiusMetric
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (r : ℝ) (hr : r ≠ 0)
    (hs : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source)
    (hcoeff : ∀ θ : S,
      gE.euclideanCoefficients (GreenMass.SphereMeasure.dilation r θ) =
        g.pullbackCoefficients e (GreenMass.SphereMeasure.dilation r θ)) :
    chartRadiusMetric g e he hei r hr hs = gaussRadiusMetric gE r hr := by
  have hinner : (chartRadiusMetric g e he hei r hr hs).inner =
      (gaussRadiusMetric gE r hr).inner := by
    funext θ
    ext v w
    exact chartRadiusMetric_inner_eq_gaussRadiusMetric g gE e he hei r hr hs θ v w
      (hcoeff θ)
  exact metric_eq_of_inner_eq hinner

/-- The retained Euclidean metric density is the actual native chart
volume density whenever their actual coefficient forms agree. -/
theorem pullbackVolumeDensity_eq_of_coefficients
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : E → M) (x : E)
    (hcoeff : gE.euclideanCoefficients x = g.pullbackCoefficients e x) :
    gE.pullbackVolumeDensity id x = g.pullbackVolumeDensity e x := by
  rw [pullbackVolumeDensity_id]
  unfold RiemannianMetric.tangentVolumeDensity RiemannianMetric.pullbackVolumeDensity
  congr 2
  ext i j
  have h := congrArg (fun B => B (EuclideanSpace.basisFun (Fin 3) ℝ i)
    (EuclideanSpace.basisFun (Fin 3) ℝ j)) hcoeff
  exact h

/-- The original manifold chart sphere has exactly the native chart-density
weighted physical area measure. All data refer to the same g,e,gE. -/
theorem chartRadiusMetric_volume_eq_native_density
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (r : ℝ) (hr : r ≠ 0)
    (hs : ∀ θ : S, GreenMass.SphereMeasure.dilation r θ ∈ e.source)
    (hcoeff : ∀ θ : S,
      gE.euclideanCoefficients (GreenMass.SphereMeasure.dilation r θ) =
        g.pullbackCoefficients e (GreenMass.SphereMeasure.dilation r θ))
    (hGauss : ∀ (θ : S) (w : E), gE.inner (GreenMass.SphereMeasure.dilation r θ)
      (GreenMass.SphereMeasure.dilation r θ) w =
        inner ℝ (GreenMass.SphereMeasure.dilation r θ) w) :
    (chartRadiusMetric g e he hei r hr hs).volumeMeasure =
      (ENNReal.ofReal (r ^ 2) • (volume : Measure E).toSphere).withDensity
        (fun θ : S => ENNReal.ofReal
          (g.pullbackVolumeDensity e (GreenMass.SphereMeasure.dilation r θ))) := by
  rw [chartRadiusMetric_eq_gaussRadiusMetric g gE e he hei r hr hs hcoeff,
    gaussRadiusMetric_volume_eq_weighted_polarArea gE r hr hGauss]
  congr 1
  funext θ
  rw [pullbackVolumeDensity_eq_of_coefficients g gE e _ (hcoeff θ)]

#print axioms chartRadiusMetric_eq_gaussRadiusMetric
#print axioms chartRadiusMetric_volume_eq_native_density

end Yamabe3.Analysis.NativeChartSphereMetric
