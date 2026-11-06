import Yamabe3.Analysis.NativePhysicalCauchyC2
import Yamabe3.Analysis.NativeActualJacobianSolver

/-! Literal native value and normal data of the same scaled C2 solution.
No ambient a.e. relation is restricted to the boundary. The negative
normal is the exterior orientation; the interior flux is its negative. -/
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
variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem same_scaled_C2_native_cauchy
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r:ℝ} (hr:0<r) (hSphere:∀θ:S,r • (θ:E)∈e.source)
    {F:E→ℝ} (hF:ContDiffOn ℝ 2 F ({(0:E)}ᶜ)) :
    let W:=coordinateExtension e (fun y:E=>F (r⁻¹ • y))
    (∀θ:S,W (e (r • (θ:E)))=F θ) ∧
    (∀θ:S,r*nativeExteriorNormalFluxFunction e r W θ=
      -8*fderiv ℝ F (θ:E) (θ:E)) ∧
    Continuous (nativeExteriorNormalFluxFunction e r W) ∧
    MemLp (nativeExteriorNormalFluxFunction e r W) 2
      (chartRadiusMetric g e he hei r hr.ne' hSphere).volumeMeasure := by
  dsimp only
  let W:=coordinateExtension e (fun y:E=>F (r⁻¹ • y))
  have ht (θ:S): (θ:E)≠0:=by
    have hn:‖(θ:E)‖=1:=by simpa only [mem_sphere,dist_zero_right] using θ.property
    intro h
    rw [h,norm_zero] at hn
    norm_num at hn
  have hs (θ:S):ContDiffAt ℝ 2 (fun y:E=>F (r⁻¹ • y)) (r • (θ:E)):=by
    apply ContDiffAt.comp _ _ (contDiff_id.const_smul r⁻¹).contDiffAt
    simpa only [id_eq,smul_smul,inv_mul_cancel₀ hr.ne',one_smul] using
      hF.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds (ht θ))
  have hW (θ:S):ContMDiffAt (𝓡 3) 𝓘(ℝ,ℝ) 2 W (e (r • (θ:E))):=by
    have hh:ContMDiffAt (𝓡 3) 𝓘(ℝ,ℝ) 2 (fun y:E=>F (r⁻¹ • y))
        (e.symm (e (r • (θ:E)))):=by
      rw [e.left_inv (hSphere θ)]
      exact (hs θ).contMDiffAt
    apply ContMDiffAt.congr_of_eventuallyEq _
      (coordinateExtension_eventuallyEq e _ (e.map_source (hSphere θ)))
    exact hh.comp _ ((hei.contMDiffAt (e.open_target.mem_nhds (e.map_source (hSphere θ)))).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  refine ⟨?_,?_,(continuous_native_local_sphere_cauchy_C2 e he hr hSphere hW).2,
    memLp_native_local_normal_C2 g e he hei hr hSphere hW⟩
  · intro θ
    change coordinateExtension e _ (e (r • (θ:E)))=_
    rw [coordinateExtension_comp_apply e _ (hSphere θ)]
    simp only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
  · intro θ
    rw [scaled_native_exterior_normal_flux_eq_C2 e he hr θ (hSphere θ) (hW θ)]
    have hnear:(fun y:E=>W (e (r • y))) =ᶠ[𝓝 (θ:E)] F:=by
      have hn:(fun y:E=>r • y) ⁻¹' e.source∈𝓝 (θ:E):=
        (e.open_source.preimage (continuous_id.const_smul r)).mem_nhds (hSphere θ)
      filter_upwards [hn] with y hy
      change coordinateExtension e _ (e (r • y))=F y
      rw [coordinateExtension_comp_apply e _ hy]
      simp only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
    rw [hnear.fderiv_eq]

#print axioms same_scaled_C2_native_cauchy
end Yamabe3.Analysis
