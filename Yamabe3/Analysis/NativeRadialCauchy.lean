import Yamabe3.Analysis.NativeDelaunayApproximation

/-!
# Physical radial Cauchy data in an actual normal chart

The radial vector is the actual chart differential of x/|x|. Its native
metric length is one, it is orthogonal to every actual angular differential,
and it differentiates the native chart radius to one. The same vector is
used for the actual manifold derivative of the end profile. No coordinate
derivative is substituted for a physical normal derivative without proof.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Yamabe3.Analysis.Delaunay

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]

def chartRadialNormal (e : OpenPartialHomeomorph E3 M) (x : E3) :
    TangentSpace (𝓡 3) (e x) :=
  mfderiv (𝓡 3) (𝓡 3) e x (‖x‖⁻¹ • x)

theorem chartRadialNormal_pairing (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E3 M) (x w : E3)
    (hGauss : ∀ a : E3, g.pullbackCoefficients e x x a = inner ℝ x a) :
    g.inner (e x) (chartRadialNormal e x) (mfderiv (𝓡 3) (𝓡 3) e x w) =
      ‖x‖⁻¹ * inner ℝ x w := by
  change g.pullbackCoefficients e x (‖x‖⁻¹ • x) w = _
  rw [map_smul, smul_apply, smul_eq_mul, hGauss]

theorem chartRadialNormal_unit (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E3 M) {x : E3} (hx : x ≠ 0)
    (hGauss : ∀ a : E3, g.pullbackCoefficients e x x a = inner ℝ x a) :
    g.inner (e x) (chartRadialNormal e x) (chartRadialNormal e x) = 1 := by
  calc
    _ = ‖x‖⁻¹ * inner ℝ x (‖x‖⁻¹ • x) :=
      chartRadialNormal_pairing g e x (‖x‖⁻¹ • x) hGauss
    _ = 1 := by
      rw [inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [norm_ne_zero_iff.mpr hx]

theorem chartRadialNormal_orthogonal (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E3 M) (x w : E3)
    (hGauss : ∀ a : E3, g.pullbackCoefficients e x x a = inner ℝ x a)
    (htangent : inner ℝ x w = 0) :
    g.inner (e x) (chartRadialNormal e x) (mfderiv (𝓡 3) (𝓡 3) e x w) = 0 := by
  rw [chartRadialNormal_pairing g e x w hGauss, htangent, mul_zero]

theorem coordinate_radial_normal_derivative
    (e : OpenPartialHomeomorph E3 M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (F : ℝ → ℝ) (hF : ContDiffOn ℝ ∞ F (Ioi 0))
    {x : E3} (hxs : x ∈ e.source) (hx : x ≠ 0) :
    mvfderiv (𝓡 3) (coordinateExtension e (fun y => F ‖y‖)) (e x)
      (chartRadialNormal e x) = deriv F ‖x‖ := by
  let u := coordinateExtension e (fun y => F ‖y‖)
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hFa := hF.contDiffAt (isOpen_Ioi.mem_nhds hp)
  have hs : ContDiffAt ℝ ∞ (fun y : E3 => F ‖y‖) x :=
    hFa.comp x (contDiffAt_norm ℝ hx)
  have hst : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y : E3 => F ‖y‖)
      (e.symm (e x)) := by rw [e.left_inv hxs]; exact hs.contMDiffAt
  have hu : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ u (e x) := by
    apply ContMDiffAt.congr_of_eventuallyEq _
      (coordinateExtension_eventuallyEq e _ (e.map_source hxs))
    exact hst.comp (e x) (hei.contMDiffAt (e.open_target.mem_nhds (e.map_source hxs)))
  have hcomp : (u ∘ e) =ᶠ[𝓝 x] (fun y : E3 => F ‖y‖) := by
    filter_upwards [e.open_source.mem_nhds hxs] with y hy
    exact coordinateExtension_comp_apply e _ hy
  have hnorm : DifferentiableAt ℝ (fun y : E3 => ‖y‖) x :=
    differentiableAt_id.norm ℝ hx
  have hN : fderiv ℝ (fun y : E3 => ‖y‖) x (‖x‖⁻¹ • x) = 1 := by
    rw [map_smul, smul_eq_mul, hnorm.fderiv_norm_self]
    exact inv_mul_cancel₀ hp.ne'
  have hd := (hFa.differentiableAt (by simp)).hasDerivAt.comp_hasFDerivAt x
    hnorm.hasFDerivAt
  change HasFDerivAt (fun y : E3 => F ‖y‖)
    (deriv F ‖x‖ • fderiv ℝ (fun y : E3 => ‖y‖) x) x at hd
  have hchain := mvfderiv_comp_apply x (hu.mdifferentiableAt (by simp))
    ((he.contMDiffAt (e.open_source.mem_nhds hxs)).mdifferentiableAt (by simp))
    (‖x‖⁻¹ • x)
  change mvfderiv (𝓡 3) (u ∘ e) x (‖x‖⁻¹ • x) = _ at hchain
  simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
    ContinuousLinearMap.comp_apply] at hchain
  change fderiv ℝ (u ∘ e) x (‖x‖⁻¹ • x) =
    mvfderiv (𝓡 3) u (e x) (chartRadialNormal e x) at hchain
  rw [hcomp.fderiv_eq, hd.fderiv] at hchain
  simp only [smul_apply, smul_eq_mul, hN, mul_one] at hchain
  exact hchain.symm

/-- The actual radius increases in this unit normal direction, fixing the
outward orientation of the boundary sphere of the chart ball. -/
theorem chartRadialNormal_outward
    (e : OpenPartialHomeomorph E3 M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {x : E3} (hxs : x ∈ e.source) (hx : x ≠ 0) :
    mvfderiv (𝓡 3) (coordinateExtension e (fun y : E3 => ‖y‖)) (e x)
      (chartRadialNormal e x) = 1 := by
  simpa only [id_eq, deriv_id] using
    coordinate_radial_normal_derivative e he hei id contDiffOn_id hxs hx

/-- Genuine manifold Cauchy data of the periodic end on a normal-coordinate
sphere. The Robin combination is exactly the physical time derivative. -/
theorem native_delaunay_cauchy_data
    (e : OpenPartialHomeomorph E3 M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (τ : ℝ)
    {x : E3} (hxs : x ∈ e.source) (hx : x ≠ 0) :
    let u := coordinateExtension e (fun y => radialProfile v τ ‖y‖)
    u (e x) = radialScale ‖x‖ * v (τ - Real.log ‖x‖) ∧
    mvfderiv (𝓡 3) u (e x) (chartRadialNormal e x) =
      -(radialScale ‖x‖ / ‖x‖) *
        (v (τ - Real.log ‖x‖) / 2 + deriv v (τ - Real.log ‖x‖)) ∧
    ‖x‖ * mvfderiv (𝓡 3) u (e x) (chartRadialNormal e x) + u (e x) / 2 =
      -radialScale ‖x‖ * deriv v (τ - Real.log ‖x‖) := by
  dsimp only
  have hd := coordinate_radial_normal_derivative e he hei _
    (radialProfile_contDiffOn hv τ) hxs hx
  rw [radialProfile_deriv hv τ (norm_pos_iff.mpr hx)] at hd
  refine ⟨?_, hd, ?_⟩
  · exact coordinateExtension_comp_apply e _ hxs
  · rw [hd, coordinateExtension_comp_apply e _ hxs]
    unfold radialProfile
    field_simp [norm_ne_zero_iff.mpr hx]
    ring

#print axioms chartRadialNormal_unit
#print axioms chartRadialNormal_orthogonal
#print axioms coordinate_radial_normal_derivative
#print axioms chartRadialNormal_outward
#print axioms native_delaunay_cauchy_data

end Yamabe3.Analysis.Delaunay
