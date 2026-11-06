import Yamabe3.Analysis.Cylinder.NativeFiniteC1PhysicalEquation
import Yamabe3.Analysis.Cylinder.NativeFiniteAngularEnergy
import PoincareLib.Geometry.Riemannian.ScalarOperators.GradientTime
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Actual Euclidean gradient energy of the same finite C2 physical fields

The ordinary Frechet derivative is evaluated on the existing genuine
radial/tangential orthonormal basis. The sphere inclusion and dilation
chain rules identify the tangential derivatives with the actual native
sphere differential. The radial slice of the original physical field
has derivative `-radialScale r / r` times the finite sum with coefficients
`q_i' + q_i / 2`.

Parseval for the true ambient orthonormal basis and the already proved
native angular energy identity then compute the actual coordinate
gradient square integral. Scalar coefficients need C2 only at the
relevant time; the positive-time theorem uses only C2 on `Ioi 0`.
The final logarithmic slice formula includes the actual Jacobian weight.
It does not identify an abstract Hilbert energy with a physical gradient
without the differential calculation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Geometry.Riemannian.SpaceForm
open PoincareMT.LeviCivitaData.Dirichlet

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local instance sphereDimensionGradientEnergy : Fact (Module.finrank ℝ E = 2 + 1) :=
  ⟨by simp [E]⟩

/-- The square sum of the actual coordinate derivatives equals the
square sum in the genuine radial/tangential ambient orthonormal basis. -/
theorem native_fderiv_square_eq_radialFrame (f : E → ℝ) (y : E) (θ : S) :
    (∑ j : Fin 3, (fderiv ℝ f y (EuclideanSpace.single j 1)) ^ 2) =
      (fderiv ℝ f y (θ : E)) ^ 2 +
        ∑ i : SphereTangentIndex θ,
          (fderiv ℝ f y
            (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S → E) θ
              ((roundSphereMetric 2).orthonormalBasis θ i))) ^ 2 := by
  calc
    _ = ‖fderiv ℝ f y‖ ^ 2 := by
      simpa only [EuclideanSpace.basisFun_apply] using
        ((EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual (fderiv ℝ f y)).symm
    _ = ∑ i : Option (SphereTangentIndex θ),
        (fderiv ℝ f y (radialTangentialBasis θ i)) ^ 2 :=
      (radialTangentialBasis θ).norm_dual (fderiv ℝ f y)
    _ = _ := by
      rw [Fintype.sum_option]
      simp only [radialTangentialBasis_apply, radialTangentialFrame]

/-- The true sphere differential of an ambient radial slice is obtained
by the sphere inclusion and dilation chain rules. Only differentiability
of the original ambient function at the actual point is needed. -/
theorem native_mvfderiv_dilated_restriction {f : E → ℝ} (r : ℝ) (θ : S)
    (hf : DifferentiableAt ℝ f (r • (θ : E))) (v : TangentSpace (𝓡 2) θ) :
    mvfderiv (𝓡 2) (fun η : S => f (r • (η : E))) θ v =
      r * fderiv ℝ f (r • (θ : E))
        (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S → E) θ v) := by
  let g : E → ℝ := fun x => f (r • x)
  have hg : DifferentiableAt ℝ g (θ : E) :=
    hf.comp (θ : E) (differentiableAt_id.const_smul r)
  have hι : MDifferentiableAt (𝓡 2) (𝓡 3) (Subtype.val : S → E) θ :=
    (contMDiff_coe_sphere (E := E) (n := 2) (m := ∞) θ).mdifferentiableAt (by simp)
  calc
    _ = mvfderiv (𝓡 3) g (θ : E)
        (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S → E) θ v) :=
      mvfderiv_comp_apply θ hg.mdifferentiableAt hι v
    _ = _ := by
      simp +instances only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
      change fderiv ℝ g (θ : E)
        (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S → E) θ v) = _
      simp only [g, fderiv_comp_smul, smul_apply, smul_eq_mul]

/-- The original finite physical field has the expected actual
tangential derivative, with its literal radial scaling. -/
theorem native_finitePhysical_tangent_derivative
    (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ)
    {r : ℝ} (hr : 0 < r) (θ : S)
    (hu : DifferentiableAt ℝ (finitePhysical s q) (r • (θ : E)))
    (v : TangentSpace (𝓡 2) θ) :
    fderiv ℝ (finitePhysical s q) (r • (θ : E))
      (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S → E) θ v) =
        (radialScale r / r) *
          mvfderiv (𝓡 2) (fun η : S => finiteAngular s q (-Real.log r, η)) θ v := by
  have hslice : (fun η : S => finitePhysical s q (r • (η : E))) =
      (fun η : S => radialScale r * finiteAngular s q (-Real.log r, η)) := by
    funext η
    rw [finitePhysical_eq_lift, cylinderLift_smul _ hr]
  have h := native_mvfderiv_dilated_restriction r θ hu v
  rw [hslice, mvfderiv_const_mul] at h
  apply mul_left_cancel₀ hr.ne'
  calc
    _ = radialScale r *
        mvfderiv (𝓡 2) (fun η : S => finiteAngular s q (-Real.log r, η)) θ v := h.symm
    _ = _ := by field_simp [hr.ne'] <;> ring

private theorem finiteAngular_time_hasDerivAt
    (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ) (θ : S) (t : ℝ)
    (hq : ∀ i ∈ s, DifferentiableAt ℝ (q i) t) :
    HasDerivAt (fun a : ℝ => finiteAngular s q (a, θ))
      (finiteAngular s (fun i => deriv (q i)) (t, θ)) t := by
  simpa only [finiteAngular] using HasDerivAt.fun_sum
    (fun i hi => (hq i hi).hasDerivAt.mul_const (angularRepresentative i θ))

private theorem finiteAngular_radial_shift
    (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ) (t : ℝ) (θ : S) :
    finiteAngular s (fun i a => deriv (q i) a + q i a / 2) (t, θ) =
      finiteAngular s (fun i => deriv (q i)) (t, θ) + finiteAngular s q (t, θ) / 2 := by
  dsimp only [finiteAngular]
  rw [Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual radial derivative has the required `q' + q/2` term.
This is computed from the original finite physical radial slice. -/
theorem native_finitePhysical_radial_derivative
    (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ)
    {r : ℝ} (hr : 0 < r) (θ : S)
    (hq : ∀ i ∈ s, DifferentiableAt ℝ (q i) (-Real.log r))
    (hu : DifferentiableAt ℝ (finitePhysical s q) (r • (θ : E))) :
    fderiv ℝ (finitePhysical s q) (r • (θ : E)) (θ : E) =
      -(radialScale r / r) *
        finiteAngular s (fun i t => deriv (q i) t + q i t / 2) (-Real.log r, θ) := by
  have heq : (fun a : ℝ => finitePhysical s q (a • (θ : E))) =ᶠ[𝓝 r]
      (fun a : ℝ => radialScale a * finiteAngular s q (-Real.log a, θ)) := by
    filter_upwards [Ioi_mem_nhds hr] with a ha
    rw [finitePhysical_eq_lift, cylinderLift_smul _ ha]
  have htime := (finiteAngular_time_hasDerivAt s q θ (-Real.log r) hq).comp r
    (Real.hasDerivAt_log hr.ne').neg
  have hprod := (radialScale_hasDerivAt hr).mul htime
  rw [← deriv_radial_slice (θ : E) hu]
  calc
    _ = (-radialScale r / (2 * r)) * finiteAngular s q (-Real.log r, θ) +
        radialScale r *
          (finiteAngular s (fun i => deriv (q i)) (-Real.log r, θ) * (-r⁻¹)) :=
      (hprod.congr_of_eventuallyEq heq).deriv
    _ = _ := by
      rw [finiteAngular_radial_shift]
      field_simp [hr.ne'] <;> ring

private theorem finitePhysical_contDiffAt_of_coefficient_c2
    (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ)
    {r : ℝ} (hr : 0 < r) (θ : S)
    (hq : ∀ i ∈ s, ContDiffAt ℝ 2 (q i) (-Real.log r)) :
    ContDiffAt ℝ 2 (finitePhysical s q) (r • (θ : E)) := by
  have hn : ‖r • (θ : E)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
  have hx : r • (θ : E) ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact hr.ne')
  unfold finitePhysical
  apply ContDiffAt.sum
  intro i hi
  exact contDiffAt_cylinderLift_separable_of_c2 (smooth_angularRepresentative i) hx
    (by simpa only [hn] using hq i hi)

/-- Pointwise energy of the actual finite physical gradient. The native
sphere gradient is the one already used by the angular spectral energy. -/
theorem native_finitePhysical_gradient_square_of_c2_at
    (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ)
    {r : ℝ} (hr : 0 < r) (θ : S)
    (hq : ∀ i ∈ s, ContDiffAt ℝ 2 (q i) (-Real.log r)) :
    (∑ j : Fin 3,
      (fderiv ℝ (finitePhysical s q) (r • (θ : E)) (EuclideanSpace.single j 1)) ^ 2) =
      (r ^ 3)⁻¹ *
        (finiteAngular s (fun i t => deriv (q i) t + q i t / 2) (-Real.log r, θ) ^ 2 +
          (roundSphereMetric 2).inner θ
            (sphereD.gradient (fun η : S => finiteAngular s q (-Real.log r, η)) θ)
            (sphereD.gradient (fun η : S => finiteAngular s q (-Real.log r, η)) θ)) := by
  have hu := (finitePhysical_contDiffAt_of_coefficient_c2 s q hr θ hq).differentiableAt
    (by norm_num)
  have hrad := native_finitePhysical_radial_derivative s q hr θ
    (fun i hi => (hq i hi).differentiableAt (by norm_num)) hu
  have htan (i : SphereTangentIndex θ) := native_finitePhysical_tangent_derivative s q hr θ hu
    ((roundSphereMetric 2).orthonormalBasis θ i)
  have hscale : (radialScale r / r) ^ 2 = (r ^ 3)⁻¹ := by
    rw [div_pow, radialScale_sq hr]
    field_simp [hr.ne'] <;> ring
  rw [native_fderiv_square_eq_radialFrame (finitePhysical s q) (r • (θ : E)) θ, hrad]
  simp_rw [htan, mul_pow]
  rw [neg_sq, ← Finset.mul_sum, ← sphereD.gradient_normSq_eq_sum_mvfderiv_sq,
    ← mul_add, hscale]

/-- Angular integration of the actual Euclidean gradient has precisely
the original finite coefficient energy, including the radial half-shift.
The genuine integrability assertion is proved before the integral value. -/
theorem native_finitePhysical_gradient_square_integral
    (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ)
    (hq : ∀ i ∈ s, ContDiffOn ℝ 2 (q i) (Ioi 0))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Integrable (fun θ : S => ∑ j : Fin 3,
      (fderiv ℝ (finitePhysical s q) (r • (θ : E)) (EuclideanSpace.single j 1)) ^ 2)
        angularVolume ∧
    (∫ θ : S, (∑ j : Fin 3,
      (fderiv ℝ (finitePhysical s q) (r • (θ : E)) (EuclideanSpace.single j 1)) ^ 2)
        ∂angularVolume) =
      (r ^ 3)⁻¹ * (∑ i ∈ s,
        ((deriv (q i) (-Real.log r) + q i (-Real.log r) / 2) ^ 2 +
          angularEigenvalue i * q i (-Real.log r) ^ 2)) := by
  let t := -Real.log r
  let qR : AngularIndex → ℝ → ℝ := fun i a => deriv (q i) a + q i a / 2
  have ht : 0 < t := neg_pos.mpr (Real.log_neg hr hr1)
  have hqAt (i : AngularIndex) (hi : i ∈ s) : ContDiffAt ℝ 2 (q i) t :=
    (hq i hi).contDiffAt (isOpen_Ioi.mem_nhds ht)
  let φ : EnergyTest sphereD univ :=
    ⟨(fun θ : S => finiteAngular s q (t, θ)), smooth_finiteAngular_sphere s q t,
      HasCompactSupport.of_compactSpace _, subset_univ _⟩
  let ψ : EnergyTest sphereD univ :=
    ⟨(fun θ : S => finiteAngular s qR (t, θ)), smooth_finiteAngular_sphere s qR t,
      HasCompactSupport.of_compactSpace _, subset_univ _⟩
  have hR : Integrable (fun θ : S => finiteAngular s qR (t, θ) ^ 2) angularVolume := by
    simpa only [pow_two] using ψ.integrable_mul ψ
  have hA : Integrable (fun θ : S => (roundSphereMetric 2).inner θ
      (sphereD.gradient (fun η : S => finiteAngular s q (t, η)) θ)
      (sphereD.gradient (fun η : S => finiteAngular s q (t, η)) θ)) angularVolume :=
    φ.integrable_gradient φ
  have hpoint (θ : S) := native_finitePhysical_gradient_square_of_c2_at s q hr θ hqAt
  have hI := (hR.add hA).const_mul ((r ^ 3)⁻¹)
  refine ⟨hI.congr (Eventually.of_forall fun θ => (hpoint θ).symm), ?_⟩
  calc
    _ = ∫ θ : S, (r ^ 3)⁻¹ *
        (finiteAngular s qR (t, θ) ^ 2 + (roundSphereMetric 2).inner θ
          (sphereD.gradient (fun η : S => finiteAngular s q (t, η)) θ)
          (sphereD.gradient (fun η : S => finiteAngular s q (t, η)) θ)) ∂angularVolume :=
      integral_congr_ae (Eventually.of_forall hpoint)
    _ = (r ^ 3)⁻¹ *
        ((∫ θ : S, finiteAngular s qR (t, θ) ^ 2 ∂angularVolume) +
          ∫ θ : S, (roundSphereMetric 2).inner θ
            (sphereD.gradient (fun η : S => finiteAngular s q (t, η)) θ)
            (sphereD.gradient (fun η : S => finiteAngular s q (t, η)) θ) ∂angularVolume) := by
      rw [integral_const_mul, integral_add hR hA]
    _ = _ := by
      simp only [integral_finiteAngular_square_eq_sum, integral_finiteAngular_gradient_square,
        ← Finset.sum_add_distrib, qR, t]

/-- The actual log-polar Jacobian cancels the actual radial gradient
scaling. This is the positive-time slice used for physical energy. -/
theorem native_finitePhysical_gradient_log_slice
    (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ)
    (hq : ∀ i ∈ s, ContDiffOn ℝ 2 (q i) (Ioi 0)) {t : ℝ} (ht : 0 < t) :
    Real.exp (-3 * t) *
      (∫ θ : S, (∑ j : Fin 3,
        (fderiv ℝ (finitePhysical s q) (Real.exp (-t) • (θ : E))
          (EuclideanSpace.single j 1)) ^ 2) ∂angularVolume) =
        (∑ i ∈ s,
          ((deriv (q i) t + q i t / 2) ^ 2 + angularEigenvalue i * q i t ^ 2)) := by
  have hr1 : Real.exp (-t) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (neg_lt_zero.mpr ht)
  have h := (native_finitePhysical_gradient_square_integral s q hq (Real.exp_pos _) hr1).2
  rw [Real.log_exp, neg_neg] at h
  rw [h, ← mul_assoc]
  have hpow : Real.exp (-t) ^ 3 = Real.exp (-3 * t) := by
    rw [pow_succ, pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hpow, mul_inv_cancel₀ (Real.exp_pos _).ne', one_mul]

#print axioms native_fderiv_square_eq_radialFrame
#print axioms native_mvfderiv_dilated_restriction
#print axioms native_finitePhysical_tangent_derivative
#print axioms native_finitePhysical_radial_derivative
#print axioms native_finitePhysical_gradient_square_of_c2_at
#print axioms native_finitePhysical_gradient_square_integral
#print axioms native_finitePhysical_gradient_log_slice

end Yamabe3.Analysis.SpherePolar
