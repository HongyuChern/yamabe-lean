import Yamabe3.Analysis.NativeRadialCauchy
import Yamabe3.Analysis.EuclideanNormalTrace

/-!
# The actual chart normal derivative for an arbitrary smooth correction

Unlike the radial-profile calculation, this applies to every smooth local
function.  It identifies the manifold derivative of coordinateExtension
in the already defined chartRadialNormal with its true Euclidean radial
derivative.  The earlier Gauss lemma proves this vector is a unit normal
in a normal chart; the present integral still uses Euclidean r²dω.
There is no assertion about a weak conormal or the surface area of g.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal

namespace Yamabe3.Analysis.Delaunay

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet
open EuclideanSphereTrace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- The actual manifold function is differentiated in the existing chart
normal, by the native scalar chain rule; no extension is substituted. -/
theorem native_chartRadialNormal_derivative
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    {f : M → ℝ} {x : E} (hxs : x ∈ e.source)
    (hf : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ f (e x)) :
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

theorem native_sphere_normal_derivative
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    {f : M → ℝ} {r : ℝ} (hr : 0 < r) (θ : S)
    (hxs : r • (θ : E) ∈ e.source)
    (hf : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ f (e (r • (θ : E)))) :
    mvfderiv (𝓡 3) f (e (r • (θ : E)))
      (chartRadialNormal e (r • (θ : E))) = fderiv ℝ (f ∘ e) (r • (θ : E)) (θ : E) := by
  rw [native_chartRadialNormal_derivative e he hxs hf,
    norm_sphereTrace_radial θ hr.le, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

theorem coordinateExtension_chartRadialNormal_derivative
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {f : E → ℝ} {x : E} (hxs : x ∈ e.source) (hf : ContDiffAt ℝ ∞ f x) :
    mvfderiv (𝓡 3) (coordinateExtension e f) (e x) (chartRadialNormal e x) =
      fderiv ℝ f x (‖x‖⁻¹ • x) := by
  let u := coordinateExtension e f
  have hst : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ f (e.symm (e x)) := by
    rw [e.left_inv hxs]
    exact hf.contMDiffAt
  have hu : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ u (e x) := by
    apply ContMDiffAt.congr_of_eventuallyEq _
      (coordinateExtension_eventuallyEq e _ (e.map_source hxs))
    exact hst.comp (e x)
      (hei.contMDiffAt (e.open_target.mem_nhds (e.map_source hxs)))
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

theorem coordinateExtension_sphere_normal_derivative
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {f : E → ℝ} {r : ℝ} (hr : 0 < r) (θ : S)
    (hxs : r • (θ : E) ∈ e.source)
    (hf : ContDiffAt ℝ ∞ f (r • (θ : E))) :
    mvfderiv (𝓡 3) (coordinateExtension e f) (e (r • (θ : E)))
      (chartRadialNormal e (r • (θ : E))) = fderiv ℝ f (r • (θ : E)) (θ : E) := by
  rw [coordinateExtension_chartRadialNormal_derivative e he hei hxs hf]
  have hnorm : ‖r • (θ : E)‖ = r := norm_sphereTrace_radial θ hr.le
  rw [hnorm, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

theorem integral_chart_normal_sq_le_scaled_hessian_energy
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r : ℝ} (hr : 0 < r)
    (hK : sphereTraceAnnulus (r / 2) (3 * r / 2) ⊆ e.source)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f e.source) :
    (∫ θ : S,
      (mvfderiv (𝓡 3) (coordinateExtension e f) (e (r • (θ : E)))
        (chartRadialNormal e (r • (θ : E)))) ^ 2
      ∂((ENNReal.ofReal (r ^ 2)) • angularVolume)) ≤
      (24 / r) * ∫ x in sphereTraceAnnulus (r / 2) (3 * r / 2),
        ‖fderiv ℝ f x‖ ^ 2 + r ^ 2 * ‖fderiv ℝ (fderiv ℝ f) x‖ ^ 2 := by
  have hs (θ : S) : r • (θ : E) ∈ e.source := by
    apply hK
    apply radial_mem_sphereTraceAnnulus (by positivity : 0 < r / 2) _ θ
    constructor <;> linarith only [hr]
  have heq (θ : S) := coordinateExtension_sphere_normal_derivative e he hei hr θ
    (hs θ) (hf.contDiffAt (e.open_source.mem_nhds (hs θ)))
  simp_rw [heq]
  exact integral_physical_sphere_normal_sq_le_scaled_hessian_energy hr e.open_source hK hf

#print axioms native_chartRadialNormal_derivative
#print axioms native_sphere_normal_derivative
#print axioms coordinateExtension_chartRadialNormal_derivative
#print axioms coordinateExtension_sphere_normal_derivative
#print axioms integral_chart_normal_sq_le_scaled_hessian_energy

end Yamabe3.Analysis.Delaunay
