import Yamabe3.Analysis.NativeManifoldOperatorC2
import Yamabe3.Analysis.NativeSolvedC2Cauchy

/-! The actual C2 scaled field, its native Laplacian and physical
Jacobian share one coordinate extension. Smoothness of the metric/chart
does not upgrade the scalar to infinite smoothness. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff Bundle
namespace Yamabe3.Analysis.ChartOperatorTransfer
open NativeC2Operators PoincareMT.LeviCivitaData.Dirichlet
open EuclideanSphereTrace Delaunay UniformElliptic
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M:Type*} [TopologicalSpace M]
  [ChartedSpace (E 3) M] [IsManifold (𝓡 3) ∞ M]

theorem laplacian_comp_of_chart_coefficients_C2
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 (E 3))
    (D:LeviCivitaData g) (DE:LeviCivitaData gE)
    (e:OpenPartialHomeomorph (E 3) M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {U:Set (E 3)} (hU:IsOpen U) (hs:U⊆e.source)
    (hcoeff:∀y∈U,gE.euclideanCoefficients y=g.pullbackCoefficients e y)
    {x:E 3} (hx:x∈U) {u:M→ℝ} (hu:ContMDiffAt (𝓡 3) 𝓘(ℝ,ℝ) 2 u (e x)):
    DE.laplacian (u∘e) x=D.laplacian u (e x):=by
  have hD:e.MDifferentiable (𝓡 3) (𝓡 3):=
    ⟨he.mdifferentiableOn (by simp),hei.mdifferentiableOn (by simp)⟩
  apply laplacian_comp_of_metric_pullback_C2 DE D
    (he.contMDiffAt (e.open_source.mem_nhds (hs hx))) ?_ ?_ hu
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact ⟨hD.mfderiv (hs hy),rfl⟩
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact metric_pairing_of_coefficients g gE e y (hcoeff y hy)

theorem coordinateExtension_laplacian_C2
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 (E 3))
    (e:OpenPartialHomeomorph (E 3) M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {U:Set (E 3)} (hU:IsOpen U) (hs:U⊆e.source)
    (hcoeff:∀y∈U,gE.euclideanCoefficients y=g.pullbackCoefficients e y)
    {x:E 3} (hx:x∈U) {F:E 3→ℝ} (hF:ContDiffAt ℝ 2 F x):
    g.leviCivitaData.laplacian (coordinateExtension e F) (e x)=
      gE.leviCivitaData.laplacian F x:=by
  have hW:ContMDiffAt (𝓡 3) 𝓘(ℝ,ℝ) 2 (coordinateExtension e F) (e x):=by
    have hf:ContMDiffAt (𝓡 3) 𝓘(ℝ,ℝ) 2 F (e.symm (e x)):=by
      rw [e.left_inv (hs hx)]
      exact hF.contMDiffAt
    apply ContMDiffAt.congr_of_eventuallyEq _
      (coordinateExtension_eventuallyEq e _ (e.map_source (hs hx)))
    exact hf.comp _ ((hei.contMDiffAt (e.open_target.mem_nhds (e.map_source (hs hx)))).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hcomp:((coordinateExtension e F)∘e)=ᶠ[𝓝 x]F:=by
    filter_upwards [e.open_source.mem_nhds (hs hx)] with y hy
    exact coordinateExtension_comp_apply e F hy
  have h:=laplacian_comp_of_chart_coefficients_C2 g gE g.leviCivitaData gE.leviCivitaData
    e he hei hU hs hcoeff hx hW
  rw [gE.leviCivitaData.laplacian_eq_of_eventuallyEq hcomp] at h
  exact h.symm

theorem same_scaled_field_original_manifold_jacobian_C2
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 (E 3))
    (e:OpenPartialHomeomorph (E 3) M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {U:Set (E 3)} (hU:IsOpen U) (hs:U⊆e.source)
    (hcoeff:∀y∈U,gE.euclideanCoefficients y=g.pullbackCoefficients e y)
    (v:ℝ→ℝ) (τ:ℝ) {r:ℝ} (hr:0<r) {F:E 3→ℝ} {x:E 3}
    (hx:r • x∈U) (hx0:x≠0) (hF:ContDiffAt ℝ 2 F x):
    let W:=coordinateExtension e (fun y:E 3=>F (r⁻¹ • y))
    nativeRescaledDelaunayJacobian gE r v τ F x=
      (r^2*g.pullbackVolumeDensity e (r • x)/8)*
        (-8*g.leviCivitaData.laplacian W (e (r • x))+
          (g.leviCivitaData.scalarCurvature (e (r • x))-
            30*radialProfile v (τ+Real.log r) ‖r • x‖^4)*W (e (r • x))):=by
  dsimp only
  have hw:ContDiffAt ℝ 2 (fun y:E 3=>F (r⁻¹ • y)) (r • x):=by
    apply ContDiffAt.comp _ _ (contDiff_id.const_smul r⁻¹).contDiffAt
    simpa only [id_eq,smul_smul,inv_mul_cancel₀ hr.ne',one_smul] using hF
  rw [native_same_scaled_field_actual_jacobian gE v τ hr hF hx0,
    coordinateExtension_laplacian_C2 g gE e he hei hU hs hcoeff hx hw,
    ←scalarCurvature_eq_of_chart_coefficients g gE g.leviCivitaData gE.leviCivitaData
      e he hU hs hcoeff hx,
    coordinateExtension_comp_apply e _ (hs hx)]
  simp only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
  rw [NativeChartSphereMetric.pullbackVolumeDensity_eq_of_coefficients g gE e (r • x) (hcoeff _ hx)]

#print axioms laplacian_comp_of_chart_coefficients_C2
#print axioms coordinateExtension_laplacian_C2
#print axioms same_scaled_field_original_manifold_jacobian_C2
end Yamabe3.Analysis.ChartOperatorTransfer
