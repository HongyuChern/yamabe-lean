import Yamabe3.Analysis.NativeSolvedC2Cauchy

/-! The same coordinate derivative is certified to use the actual
exterior unit normal under the actual Gauss pullback coefficients. This
keeps geometry certification separate from the mere name of a flux. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff Bundle ENNReal
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
namespace Yamabe3.Analysis
open Delaunay EuclideanSphereTrace NativeChartSphereMetric PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem same_scaled_C2_native_unit_conormal
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r:ℝ} (hr:0<r) (hs:∀θ:S,r • (θ:E)∈e.source)
    (hcoeff:∀θ:S,gE.euclideanCoefficients (r • (θ:E))=g.pullbackCoefficients e (r • (θ:E)))
    (hGauss:∀(θ:S)(v:E),gE.inner (r • (θ:E)) (r • (θ:E)) v=inner ℝ (r • (θ:E)) v)
    {F:E→ℝ} (hF:ContDiffOn ℝ 2 F ({(0:E)}ᶜ)):
    let W:=coordinateExtension e (fun y:E=>F (r⁻¹ • y))
    (∀θ:S,
      g.inner (e (r • (θ:E))) (-chartRadialNormal e (r • (θ:E))) (-chartRadialNormal e (r • (θ:E)))=1 ∧
      (∀v:E,inner ℝ (r • (θ:E)) v=0→
        g.inner (e (r • (θ:E))) (-chartRadialNormal e (r • (θ:E)))
          (mfderiv (𝓡 3) (𝓡 3) e (r • (θ:E)) v)=0) ∧
      mvfderiv (𝓡 3) (coordinateExtension e (fun y:E=>‖y‖)) (e (r • (θ:E)))
        (-chartRadialNormal e (r • (θ:E)))=-1) ∧
    (∀θ:S,W (e (r • (θ:E)))=F θ) ∧
    (∀θ:S,r*nativeExteriorNormalFluxFunction e r W θ=-8*fderiv ℝ F (θ:E) (θ:E)) ∧
    Continuous (nativeExteriorNormalFluxFunction e r W) ∧
    MemLp (nativeExteriorNormalFluxFunction e r W) 2
      (chartRadiusMetric g e he hei r hr.ne' hs).volumeMeasure:=by
  dsimp only
  refine ⟨?_,same_scaled_C2_native_cauchy g e he hei hr hs hF⟩
  intro θ
  have hx:r • (θ:E)≠0:=by
    intro hz
    have hn:=norm_sphereTrace_radial θ hr.le
    rw [hz,norm_zero] at hn
    linarith
  apply nativeExteriorNormal_geometry g e he hei (hs θ) hx
  intro v
  rw [←hcoeff θ]
  exact hGauss θ v

#print axioms same_scaled_C2_native_unit_conormal
end Yamabe3.Analysis
