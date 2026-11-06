import Yamabe3.Analysis.NativeCoordinateNormalTrace
import Yamabe3.Analysis.NativePhysicalNormalTrace

/-! Finite C1 native normal differentiation for the actual H4/C2 field.
The charts remain smooth; the solved field is not assumed infinitely smooth. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.Delaunay
open PoincareMT PoincareMT.LeviCivitaData.Dirichlet EuclideanSphereTrace
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
theorem native_chartRadialNormal_derivative_C1
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    {f : M → ℝ} {x : E} (hxs : x ∈ e.source)
    (hf : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) 1 f (e x)) :
    mvfderiv (𝓡 3) f (e x) (chartRadialNormal e x) =
      fderiv ℝ (f ∘ e) x (‖x‖⁻¹ • x) := by
  have hchain := mvfderiv_comp_apply x (hf.mdifferentiableAt (by simp))
    ((he.contMDiffAt (e.open_source.mem_nhds hxs)).mdifferentiableAt (by simp))
    (‖x‖⁻¹ • x)
  change mvfderiv (𝓡 3) (f ∘ e) x (‖x‖⁻¹ • x) = _ at hchain
  simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
    ContinuousLinearMap.comp_apply] at hchain
  change fderiv ℝ (f ∘ e) x (‖x‖⁻¹ • x) =
    mvfderiv (𝓡 3) f (e x) (chartRadialNormal e x) at hchain
  exact hchain.symm

theorem native_sphere_normal_derivative_C1
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    {f : M → ℝ} {r : ℝ} (hr : 0 < r) (θ : S)
    (hxs : r • (θ : E) ∈ e.source)
    (hf : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) 1 f (e (r • (θ : E)))) :
    mvfderiv (𝓡 3) f (e (r • (θ : E)))
      (chartRadialNormal e (r • (θ : E))) = fderiv ℝ (f ∘ e) (r • (θ : E)) (θ : E) := by
  rw [native_chartRadialNormal_derivative_C1 e he hxs hf,
    norm_sphereTrace_radial θ hr.le, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

theorem coordinateExtension_chartRadialNormal_derivative_C1
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {f : E → ℝ} {x : E} (hxs : x ∈ e.source) (hf : ContDiffAt ℝ 1 f x) :
    mvfderiv (𝓡 3) (coordinateExtension e f) (e x) (chartRadialNormal e x) =
      fderiv ℝ f x (‖x‖⁻¹ • x) := by
  let u := coordinateExtension e f
  have hst : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) 1 f (e.symm (e x)) := by
    rw [e.left_inv hxs]
    exact hf.contMDiffAt
  have hu : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) 1 u (e x) := by
    apply ContMDiffAt.congr_of_eventuallyEq _
      (coordinateExtension_eventuallyEq e _ (e.map_source hxs))
    exact hst.comp (e x)
      ((hei.contMDiffAt (e.open_target.mem_nhds (e.map_source hxs))).of_le (by simp))
  have hcomp : (u ∘ e) =ᶠ[𝓝 x] f := by
    filter_upwards [e.open_source.mem_nhds hxs] with y hy
    exact coordinateExtension_comp_apply e _ hy
  have hchain := mvfderiv_comp_apply x (hu.mdifferentiableAt (by simp))
    ((he.contMDiffAt (e.open_source.mem_nhds hxs)).mdifferentiableAt (by simp))
    (‖x‖⁻¹ • x)
  change mvfderiv (𝓡 3) (u ∘ e) x (‖x‖⁻¹ • x) = _ at hchain
  simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
    ContinuousLinearMap.comp_apply] at hchain
  change fderiv ℝ (u ∘ e) x (‖x‖⁻¹ • x) =
    mvfderiv (𝓡 3) u (e x) (chartRadialNormal e x) at hchain
  rw [hcomp.fderiv_eq] at hchain
  exact hchain.symm

theorem coordinateExtension_sphere_normal_derivative_C1
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {f : E → ℝ} {r : ℝ} (hr : 0 < r) (θ : S)
    (hxs : r • (θ : E) ∈ e.source)
    (hf : ContDiffAt ℝ 1 f (r • (θ : E))) :
    mvfderiv (𝓡 3) (coordinateExtension e f) (e (r • (θ : E)))
      (chartRadialNormal e (r • (θ : E))) = fderiv ℝ f (r • (θ : E)) (θ : E) := by
  rw [coordinateExtension_chartRadialNormal_derivative_C1 e he hei hxs hf]
  have hnorm : ‖r • (θ : E)‖ = r := norm_sphereTrace_radial θ hr.le
  rw [hnorm, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]


#print axioms native_chartRadialNormal_derivative_C1
#print axioms native_sphere_normal_derivative_C1
#print axioms coordinateExtension_chartRadialNormal_derivative_C1
#print axioms coordinateExtension_sphere_normal_derivative_C1
end Yamabe3.Analysis.Delaunay
