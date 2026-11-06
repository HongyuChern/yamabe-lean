import Yamabe3.Analysis.NativeDivergenceC2
import Yamabe3.Analysis.WeakDivergenceIdentification
import PoincareLib.Geometry.Riemannian.Splitting.Busemann.Regularity.Distribution

/-! The actual smooth coordinate divergence identity, with its density
ratio. The same physical function and native metric determine both sides. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology Manifold
namespace Yamabe3.Analysis.UniformElliptic
open PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem principalSource_eq_of_matrix_germ {a b : E → Matrix (Fin 3) (Fin 3) ℝ}
    (u : E → ℝ) {x : E} (hab : a =ᶠ[𝓝 x] b) : principalSource a u x=principalSource b u x := by
  unfold principalSource
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hh : matrixFlux a (fun j => partialDeriv j u) i =ᶠ[𝓝 x]
      matrixFlux b (fun j => partialDeriv j u) i := by
    filter_upwards [hab] with y hy
    simp only [matrixFlux,hy]
  exact congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hh.fderiv_eq

theorem principalSource_chart_eq_negative_density_laplacian
    (g : RiemannianMetric 3 E) (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) {x : E} (hx : x∈e.source) :
    principalSource (divergenceCoefficients g e) (u∘e) x=
      -g.pullbackVolumeDensity e x*D.laplacian u (e x) := by
  have hum : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ u := contMDiff_iff_contDiff.mpr hu
  have hd := D.density_mul_laplacian_eq_coordinate_divergence e he hei hx hum.contMDiffAt
  have hflux (i : Fin 3) :
      (fun y => g.pullbackVolumeDensity e y*
        WithLp.ofLp (VectorField.mpullback (𝓡 3) (𝓡 3) e (D.gradient u) y) i) =ᶠ[𝓝 x]
      matrixFlux (divergenceCoefficients g e) (fun j => partialDeriv j (u∘e)) i := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact D.coordinateGradientFlux_eq_divergenceCoefficients e he hei hy hum.contMDiffAt i
  have hs : (∑ i : Fin 3,fderiv ℝ (fun y => g.pullbackVolumeDensity e y*
      WithLp.ofLp (VectorField.mpullback (𝓡 3) (𝓡 3) e (D.gradient u) y) i) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i))=
      ∑ i : Fin 3,partialDeriv i (matrixFlux (divergenceCoefficients g e)
        (fun j => partialDeriv j (u∘e)) i) x := by
    apply Finset.sum_congr rfl
    intro i _
    simpa only [EuclideanSpace.basisFun_apply,partialDeriv] using
      congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) (hflux i).fderiv_eq
  rw [hs] at hd
  change -(∑ i : Fin 3,partialDeriv i (matrixFlux (divergenceCoefficients g e)
    (fun j => partialDeriv j (u∘e)) i) x)=_
  rw [← hd]
  ring

theorem principalSource_chart_density_ratio
    (g : RiemannianMetric 3 E) (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) {x : E} (hx : x∈e.source) :
    principalSource (divergenceCoefficients g e) (u∘e) x=
      (g.pullbackVolumeDensity e x/g.pullbackVolumeDensity id (e x))*
        principalSource (nativeDivergenceMatrix g) u (e x) := by
  rw [principalSource_chart_eq_negative_density_laplacian g g.leviCivitaData e he hei hu hx,
    native_principalSource_eq_negative_density_laplacian_C2 g g.leviCivitaData
      (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt]
  have hρ : g.pullbackVolumeDensity id (e x)≠0 := ne_of_gt ((GreenParametrix.native_density_smooth_positive g).2 (e x))
  field_simp [hρ]

#print axioms principalSource_eq_of_matrix_germ
#print axioms principalSource_chart_eq_negative_density_laplacian
#print axioms principalSource_chart_density_ratio
end Yamabe3.Analysis.UniformElliptic
