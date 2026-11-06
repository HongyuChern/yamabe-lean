import Yamabe3.Analysis.Cylinder.NativeSpectralTruncation
import Yamabe3.Analysis.Cylinder.NativeAngularFiniteApproximation
import Yamabe3.Analysis.UniformElliptic.NativeC1StrongLimit

/-!
# Actual finite angular fields with C2 scalar coefficients

The scalar coefficients need two derivatives only on positive cylinder
time. Their original finite physical field is C2 on the punctured unit
ball. At a fixed point a quadratic polynomial has the same actual two
scalar jets. Ordinary product and chain rules show that the two physical
directional derivatives agree there. The already proved native smooth
eigenmode identity therefore computes the actual coordinate trace of the
original C2 field; it is not applied to a nonsmooth coefficient.

Finally C1 integration by parts on the actual first derivatives produces
the physical weak equation. The source retains the literal factor
`physicalForcing f = -8 * cylinderLift f / norm^2`, and the physical
potential is `V (-log norm) / norm^2`. No regularity of the source beyond
that already needed to supply the actual scalar C2 equation is imposed.
No statement crosses the entrance sphere or the missing origin.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.UniformElliptic

private theorem native_second_directional_congr {f g : E → ℝ} {x : E}
    (h : f =ᶠ[𝓝 x] g) (v : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x v =
      fderiv ℝ (fun y => fderiv ℝ g y v) x v := by
  have hd : (fun y => fderiv ℝ f y v) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ g y v) :=
    (h.fderiv (𝕜 := ℝ)).mono fun _ hy => congrArg (fun L : E →L[ℝ] ℝ => L v) hy
  exact congrArg (fun L : E →L[ℝ] ℝ => L v) hd.fderiv_eq

private theorem native_directional_mul_comp_scalar
    {A T : E → ℝ} {q : ℝ → ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hT : DifferentiableAt ℝ T x)
    (hq : DifferentiableAt ℝ q (T x)) (v : E) :
    fderiv ℝ (fun y => A y * q (T y)) x v =
      fderiv ℝ A x v * q (T x) + A x * deriv q (T x) * fderiv ℝ T x v := by
  have hqc := hq.hasDerivAt.comp_hasFDerivAt x hT.hasFDerivAt
  have hprod := hA.hasFDerivAt.mul hqc
  change HasFDerivAt (fun y => A y * q (T y)) _ x at hprod
  rw [hprod.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, Function.comp_apply]
  ring

private theorem native_second_directional_mul_comp_scalar
    {A T : E → ℝ} {q : ℝ → ℝ} {x : E}
    (hA : ContDiffAt ℝ 2 A x) (hT : ContDiffAt ℝ 2 T x)
    (hq : ContDiffAt ℝ 2 q (T x)) (v : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => A z * q (T z)) y v) x v =
      fderiv ℝ (fun y => fderiv ℝ A y v) x v * q (T x) +
        2 * fderiv ℝ A x v * deriv q (T x) * fderiv ℝ T x v +
        A x * deriv (deriv q) (T x) * (fderiv ℝ T x v) ^ 2 +
        A x * deriv q (T x) * fderiv ℝ (fun y => fderiv ℝ T y v) x v := by
  have hAd := hA.differentiableAt (by norm_num)
  have hTd := hT.differentiableAt (by norm_num)
  have hqd := hq.differentiableAt (by norm_num)
  have hDA : DifferentiableAt ℝ (fun y => fderiv ℝ A y v) x :=
    ((hA.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  have hDT : DifferentiableAt ℝ (fun y => fderiv ℝ T y v) x :=
    ((hT.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  have hqdd : DifferentiableAt ℝ (deriv q) (T x) :=
    ((hq.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  have heq : (fun y => fderiv ℝ (fun z => A z * q (T z)) y v) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ A y v * q (T y) +
        A y * deriv q (T y) * fderiv ℝ T y v) := by
    have hAe := (hA.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).eventually (by simp)
    have hTe := (hT.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).eventually (by simp)
    have hqe := (hq.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).eventually (by simp)
    filter_upwards [hAe, hTe, hT.continuousAt.eventually hqe] with y hAy hTy hqy
    exact native_directional_mul_comp_scalar
      (hAy.differentiableAt (by norm_num)) (hTy.differentiableAt (by norm_num))
      (hqy.differentiableAt (by norm_num)) v
  have hqc := hqd.hasDerivAt.comp_hasFDerivAt x hTd.hasFDerivAt
  have hqdc := hqdd.hasDerivAt.comp_hasFDerivAt x hTd.hasFDerivAt
  have hsum := (hDA.hasFDerivAt.mul hqc).add
    ((hAd.hasFDerivAt.mul hqdc).mul hDT.hasFDerivAt)
  change HasFDerivAt (fun y => fderiv ℝ A y v * q (T y) +
    A y * deriv q (T y) * fderiv ℝ T y v) _ x at hsum
  rw [heq.fderiv_eq, hsum.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, Function.comp_apply, Pi.mul_apply]
  ring

private def nativeQuadraticJet (q : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  q t₀ + deriv q t₀ * (t - t₀) + deriv (deriv q) t₀ / 2 * (t - t₀) ^ 2

private theorem nativeQuadraticJet_smooth (q : ℝ → ℝ) (t₀ : ℝ) :
    ContDiff ℝ ∞ (nativeQuadraticJet q t₀) := by
  unfold nativeQuadraticJet
  fun_prop

private theorem nativeQuadraticJet_value (q : ℝ → ℝ) (t₀ : ℝ) :
    nativeQuadraticJet q t₀ t₀ = q t₀ := by
  simp only [nativeQuadraticJet, sub_self, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    add_zero]

private theorem nativeQuadraticJet_hasDerivAt (q : ℝ → ℝ) (t₀ t : ℝ) :
    HasDerivAt (nativeQuadraticJet q t₀)
      (deriv q t₀ + deriv (deriv q) t₀ * (t - t₀)) t := by
  have ht := (hasDerivAt_id t).sub_const t₀
  have h := ((hasDerivAt_const t (q t₀)).add (ht.const_mul (deriv q t₀))).add
    ((ht.pow 2).const_mul (deriv (deriv q) t₀ / 2))
  apply h.congr_deriv
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, zero_add]
  ring

private theorem nativeQuadraticJet_deriv (q : ℝ → ℝ) (t₀ t : ℝ) :
    deriv (nativeQuadraticJet q t₀) t =
      deriv q t₀ + deriv (deriv q) t₀ * (t - t₀) :=
  (nativeQuadraticJet_hasDerivAt q t₀ t).deriv

private theorem nativeQuadraticJet_second (q : ℝ → ℝ) (t₀ t : ℝ) :
    deriv (deriv (nativeQuadraticJet q t₀)) t = deriv (deriv q) t₀ := by
  rw [show deriv (nativeQuadraticJet q t₀) =
      (fun s => deriv q t₀ + deriv (deriv q) t₀ * (s - t₀)) from
    funext (nativeQuadraticJet_deriv q t₀)]
  simpa only [id_eq, mul_one] using
    ((((hasDerivAt_id t).sub_const t₀).const_mul (deriv (deriv q) t₀)).const_add
      (deriv q t₀)).deriv

private theorem native_separableLift_mul_time (q : ℝ → ℝ) (φ : S → ℝ)
    {x : E} (hx : x ≠ 0) :
    cylinderLift (separableCylinder q φ) x =
      cylinderLift (separableCylinder (fun _ => 1) φ) x * q (-Real.log ‖x‖) := by
  let y : puncturedSpace := ⟨x, by change x ≠ 0; exact hx⟩
  change cylinderLift (separableCylinder q φ) (y : E) =
    cylinderLift (separableCylinder (fun _ => 1) φ) (y : E) * q (-Real.log ‖(y : E)‖)
  simp only [cylinderLift_coe, puncturedCylinderLift, cylinderCoordinates, separableCylinder,
    one_mul]
  ring

private theorem native_separableLift_mul_time_germ (q : ℝ → ℝ) (φ : S → ℝ)
    {x : E} (hx : x ≠ 0) :
    cylinderLift (separableCylinder q φ) =ᶠ[𝓝 x]
      (fun y => cylinderLift (separableCylinder (fun _ => 1) φ) y *
        q (-Real.log ‖y‖)) := by
  filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds
    (show x ∈ ({0}ᶜ : Set E) from hx)] with y hy
  exact native_separableLift_mul_time q φ hy

private theorem native_time_contDiffAt {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : E => -Real.log ‖y‖) x :=
  ((Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr hx)).comp x
    (contDiffAt_norm ℝ hx)).neg

/-- Actual C2 regularity at the relevant scalar time is enough for the
original separable physical lift, away from the origin. -/
theorem contDiffAt_cylinderLift_separable_of_c2 {q : ℝ → ℝ} {φ : S → ℝ}
    (hφ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ φ) {x : E} (hx : x ≠ 0)
    (hq : ContDiffAt ℝ 2 q (-Real.log ‖x‖)) :
    ContDiffAt ℝ 2 (cylinderLift (separableCylinder q φ)) x := by
  have hA : ContDiffAt ℝ ∞
      (cylinderLift (separableCylinder (fun _ => 1) φ)) x :=
    contDiffAt_cylinderLift (smooth_separableCylinder contDiff_const hφ) hx
  have hT := native_time_contDiffAt hx
  have hprod : ContDiffAt ℝ 2
      (fun y => cylinderLift (separableCylinder (fun _ => 1) φ) y * q (-Real.log ‖y‖)) x :=
    (hA.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).mul
      (hq.comp x (hT.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)))
  exact hprod.congr_of_eventuallyEq (native_separableLift_mul_time_germ q φ hx)

/-- The original finite angular field is C2 on the actual punctured unit
ball. Only positive-time scalar regularity is used. -/
theorem contDiffOn_finitePhysical_of_c2_positive
    (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ)
    (hq : ∀ i ∈ s, ContDiffOn ℝ 2 (q i) (Ioi 0)) :
    ContDiffOn ℝ 2 (finitePhysical s q) {x : E | x ≠ 0 ∧ ‖x‖ < 1} := by
  intro x hx
  have ht : 0 < -Real.log ‖x‖ := neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr hx.1) hx.2)
  apply ContDiffAt.contDiffWithinAt
  apply ContDiffAt.sum
  intro i hi
  exact contDiffAt_cylinderLift_separable_of_c2 (smooth_angularRepresentative i) hx.1
    ((hq i hi).contDiffAt (isOpen_Ioi.mem_nhds ht))

/-- The finite projection of the same Hilbert curve has the same local
C2 regularity whenever its actual scalar coordinates do. -/
theorem contDiffOn_projectedAngular_lift_of_c2_positive
    (s : Finset AngularIndex) (U : ℝ → AngularL2)
    (hq : ∀ i ∈ s, ContDiffOn ℝ 2 (fun t => inner ℝ (angularBasis i) (U t)) (Ioi 0)) :
    ContDiffOn ℝ 2 (cylinderLift (projectedAngular s U))
      {x : E | x ≠ 0 ∧ ‖x‖ < 1} := by
  simpa only [finitePhysical_eq_lift, projectedAngular] using
    contDiffOn_finitePhysical_of_c2_positive s _ hq

private theorem native_second_separable_of_scalar_jets
    {q p : ℝ → ℝ} {φ : S → ℝ}
    (hφ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ φ) {x : E} (hx : x ≠ 0)
    (hq : ContDiffAt ℝ 2 q (-Real.log ‖x‖))
    (hp : ContDiffAt ℝ 2 p (-Real.log ‖x‖))
    (h0 : q (-Real.log ‖x‖) = p (-Real.log ‖x‖))
    (h1 : deriv q (-Real.log ‖x‖) = deriv p (-Real.log ‖x‖))
    (h2 : deriv (deriv q) (-Real.log ‖x‖) = deriv (deriv p) (-Real.log ‖x‖))
    (v : E) :
    fderiv ℝ (fun y => fderiv ℝ (cylinderLift (separableCylinder q φ)) y v) x v =
      fderiv ℝ (fun y => fderiv ℝ (cylinderLift (separableCylinder p φ)) y v) x v := by
  have hA : ContDiffAt ℝ 2
      (cylinderLift (separableCylinder (fun _ => 1) φ)) x :=
    (contDiffAt_cylinderLift (smooth_separableCylinder contDiff_const hφ) hx).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hT : ContDiffAt ℝ 2 (fun y : E => -Real.log ‖y‖) x :=
    (native_time_contDiffAt hx).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [native_second_directional_congr (native_separableLift_mul_time_germ q φ hx) v,
    native_second_directional_congr (native_separableLift_mul_time_germ p φ hx) v,
    native_second_directional_mul_comp_scalar hA hT hq v,
    native_second_directional_mul_comp_scalar hA hT hp v, h0, h1, h2]

private theorem native_smooth_laplacian_eq_trace {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ ∞ u x) :
    euclideanD.laplacian u x = ∑ j : Fin 3,
      fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single j 1) := by
  rw [euclideanD.laplacian_euclideanMetric hu]
  apply Finset.sum_congr rfl
  intro j _
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  simp only [EuclideanSpace.basisFun_apply]
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

private theorem native_separable_trace_of_c2_at
    {q : ℝ → ℝ} {φ : S → ℝ}
    (hφ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ φ) {μ : ℝ}
    (heigen : ∀ θ, -sphereD.laplacian φ θ = μ * φ θ)
    {r : ℝ} (hr : 0 < r) (θ : S)
    (hq : ContDiffAt ℝ 2 q (-Real.log r)) :
    (∑ j : Fin 3, fderiv ℝ
      (fun y => fderiv ℝ (cylinderLift (separableCylinder q φ)) y
        (EuclideanSpace.single j 1)) (r • (θ : E)) (EuclideanSpace.single j 1)) =
      radialScale r / r ^ 2 *
        (deriv (deriv q) (-Real.log r) - (μ + 1 / 4) * q (-Real.log r)) * φ θ := by
  have hn : ‖r • (θ : E)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
  have hx : r • (θ : E) ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact hr.ne')
  let p := nativeQuadraticJet q (-Real.log r)
  have hp : ContDiff ℝ ∞ p := nativeQuadraticJet_smooth q (-Real.log r)
  have htrace : (∑ j : Fin 3, fderiv ℝ
      (fun y => fderiv ℝ (cylinderLift (separableCylinder q φ)) y
        (EuclideanSpace.single j 1)) (r • (θ : E)) (EuclideanSpace.single j 1)) =
      euclideanD.laplacian (cylinderLift (separableCylinder p φ)) (r • (θ : E)) := by
    rw [native_smooth_laplacian_eq_trace
      (contDiffAt_cylinderLift (smooth_separableCylinder hp hφ) hx)]
    apply Finset.sum_congr rfl
    intro j _
    apply native_second_separable_of_scalar_jets hφ hx
      (by simpa only [hn] using hq)
      (hp.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    · simp only [hn, p, nativeQuadraticJet_value]
    · simp only [hn, p, nativeQuadraticJet_deriv, sub_self, mul_zero, add_zero]
    · simp only [hn, p, nativeQuadraticJet_second]
  rw [htrace]
  have h := native_yamabe_linearized_eigenmode (fun _ => 0) hp hφ heigen hr θ
  simp only [euclidean_scalarCurvature_zero, zero_mul, add_zero, radialProfile, mul_zero,
    zero_pow (by decide : (4 : ℕ) ≠ 0), sub_zero, modelJacobi] at h
  dsimp only [p] at h
  rw [nativeQuadraticJet_value, nativeQuadraticJet_second] at h
  have hscaled :
      -8 * euclideanD.laplacian (cylinderLift (separableCylinder p φ)) (r • (θ : E)) =
      -8 * (radialScale r / r ^ 2 *
        (deriv (deriv q) (-Real.log r) - (μ + 1 / 4) * q (-Real.log r)) * φ θ) := by
    calc
      _ = _ := h
      _ = _ := by ring
  linarith

private theorem native_second_directional_sum {ι : Type*} (s : Finset ι)
    (f : ι → E → ℝ) {x : E} (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) (v : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => ∑ i ∈ s, f i z) y v) x v =
      ∑ i ∈ s, fderiv ℝ (fun y => fderiv ℝ (f i) y v) x v := by
  have he : ∀ᶠ y in 𝓝 x, ∀ i ∈ s, DifferentiableAt ℝ (f i) y := by
    apply (Filter.eventually_all_finset s).mpr
    intro i hi
    exact ((hf i hi).of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).eventually (by simp) |>.mono
      fun _ h => h.differentiableAt (by norm_num)
  have heq : (fun y => fderiv ℝ (fun z => ∑ i ∈ s, f i z) y v) =ᶠ[𝓝 x]
      (fun y => ∑ i ∈ s, fderiv ℝ (f i) y v) := by
    filter_upwards [he] with y hy
    rw [fderiv_fun_sum hy]
    simp only [sum_apply]
  have hd (i) (hi : i ∈ s) : DifferentiableAt ℝ (fun y => fderiv ℝ (f i) y v) x :=
    (((hf i hi).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  rw [heq.fderiv_eq, fderiv_fun_sum hd]
  simp only [sum_apply]

/-- The actual coordinate trace of the original finite C2 physical field
is the native angular spectral expression. -/
theorem native_finitePhysical_trace_of_c2_at
    (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ)
    {r : ℝ} (hr : 0 < r) (θ : S)
    (hq : ∀ i ∈ s, ContDiffAt ℝ 2 (q i) (-Real.log r)) :
    (∑ j : Fin 3, fderiv ℝ
      (fun y => fderiv ℝ (finitePhysical s q) y (EuclideanSpace.single j 1))
        (r • (θ : E)) (EuclideanSpace.single j 1)) =
      radialScale r / r ^ 2 * ∑ i ∈ s,
        (deriv (deriv (q i)) (-Real.log r) -
          (angularEigenvalue i + 1 / 4) * q i (-Real.log r)) * angularRepresentative i θ := by
  have hn : ‖r • (θ : E)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
  have hx : r • (θ : E) ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact hr.ne')
  have hC2 (i) (hi : i ∈ s) : ContDiffAt ℝ 2
      (cylinderLift (separableCylinder (q i) (angularRepresentative i))) (r • (θ : E)) :=
    contDiffAt_cylinderLift_separable_of_c2 (smooth_angularRepresentative i) hx
      (by simpa only [hn] using hq i hi)
  change (∑ j : Fin 3, fderiv ℝ
    (fun y => fderiv ℝ (fun z => ∑ i ∈ s,
      cylinderLift (separableCylinder (q i) (angularRepresentative i)) z) y
        (EuclideanSpace.single j 1)) (r • (θ : E)) (EuclideanSpace.single j 1)) = _
  simp_rw [native_second_directional_sum s _ hC2]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [mul_assoc] using native_separable_trace_of_c2_at
    (smooth_angularRepresentative i) (angularRepresentative_equation i) hr θ (hq i hi)

/-- The scalar coefficient ODE gives the normalized physical source for
the same finite physical field. The potential is exactly r^-2 V(-log r). -/
theorem native_finitePhysical_negative_trace_eq
    (V : ℝ → ℝ) (s : Finset AngularIndex) (q f : AngularIndex → ℝ → ℝ)
    (hq : ∀ i ∈ s, ContDiffOn ℝ 2 (q i) (Ioi 0))
    (heq : ∀ i ∈ s, ∀ t, 0 < t →
      deriv (deriv (q i)) t = (angularEigenvalue i + 1 / 4 - V t) * q i t + f i t)
    {x : E} (hx : x ≠ 0) (hx1 : ‖x‖ < 1) :
    -(∑ j : Fin 3, fderiv ℝ
      (fun y => fderiv ℝ (finitePhysical s q) y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single j 1)) =
      physicalForcing (finiteAngular s f) x / 8 +
        (V (-Real.log ‖x‖) / ‖x‖ ^ 2) * finitePhysical s q x := by
  let y : puncturedSpace := ⟨x, by change x ≠ 0; exact hx⟩
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have ht : 0 < -Real.log ‖x‖ := neg_pos.mpr (Real.log_neg hr hx1)
  have htrace := native_finitePhysical_trace_of_c2_at s q hr (sphereDirection y)
    (fun i hi => (hq i hi).contDiffAt (isOpen_Ioi.mem_nhds ht))
  rw [norm_smul_sphereDirection y] at htrace
  have hsum : (∑ i ∈ s, (deriv (deriv (q i)) (-Real.log ‖x‖) -
      (angularEigenvalue i + 1 / 4) * q i (-Real.log ‖x‖)) *
        angularRepresentative i (sphereDirection y)) =
      (∑ i ∈ s, f i (-Real.log ‖x‖) * angularRepresentative i (sphereDirection y)) -
        V (-Real.log ‖x‖) *
          (∑ i ∈ s, q i (-Real.log ‖x‖) * angularRepresentative i (sphereDirection y)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [heq i hi _ ht]
    ring
  rw [htrace, hsum, finitePhysical_eq_lift]
  change _ = physicalForcing (finiteAngular s f) (y : E) / 8 +
    (V (-Real.log ‖x‖) / ‖x‖ ^ 2) * cylinderLift (finiteAngular s q) (y : E)
  rw [physicalForcing, cylinderLift_coe, cylinderLift_coe]
  simp only [puncturedCylinderLift, cylinderCoordinates, finiteAngular]
  change _ = (-8 * (radialScale ‖x‖ *
      (∑ i ∈ s, f i (-Real.log ‖x‖) * angularRepresentative i (sphereDirection y))) /
      ‖x‖ ^ 2) / 8 + (V (-Real.log ‖x‖) / ‖x‖ ^ 2) *
      (radialScale ‖x‖ *
        (∑ i ∈ s, q i (-Real.log ‖x‖) * angularRepresentative i (sphereDirection y)))
  ring

private theorem native_C2_integral_gradient_eq_negative_trace
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u Ω)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) :
    (∫ x in Ω, ∑ j : Fin 3,
      fderiv ℝ u x (EuclideanSpace.single j 1) *
        fderiv ℝ φ x (EuclideanSpace.single j 1)) =
      ∫ x in Ω, (-(∑ j : Fin 3,
        fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single j 1))) * φ x := by
  let p (j : Fin 3) (x : E) := fderiv ℝ u x (EuclideanSpace.single j 1)
  let pp (j : Fin 3) (x : E) := fderiv ℝ (p j) x (EuclideanSpace.single j 1)
  have hp (j : Fin 3) : ContDiffOn ℝ 1 (p j) Ω := by
    intro x hx
    exact (((hu.contDiffAt (hΩ.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).contDiffWithinAt
  have hpp (j : Fin 3) : ContinuousOn (pp j) Ω :=
    ((hp j).continuousOn_fderiv_of_isOpen hΩ (by norm_num)).clm_apply continuousOn_const
  have hfirst (j : Fin 3) : IntegrableOn
      (fun x => p j x * fderiv ℝ φ x (EuclideanSpace.single j 1)) Ω := by
    apply Integrable.integrableOn
    apply Continuous.integrable_of_hasCompactSupport _
      (hc.fderiv_apply ℝ (EuclideanSpace.single j 1)).mul_left
    have hdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    exact ((hp j).continuousOn.mul hdφ.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans
        ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j 1)).trans hs))
  have hsecond (j : Fin 3) : IntegrableOn (fun x => pp j x * φ x) Ω := by
    apply Integrable.integrableOn
    apply Continuous.integrable_of_hasCompactSupport _ hc.mul_left
    exact ((hpp j).mul hφ.continuous.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hs)
  have hi (j : Fin 3) :
      (∫ x in Ω, p j x * fderiv ℝ φ x (EuclideanSpace.single j 1)) =
        -(∫ x in Ω, pp j x * φ x) :=
    native_hasWeakPartialDeriv_of_contDiffOn_one hΩ (hp j) j φ hφ hc hs
  change (∫ x in Ω, ∑ j : Fin 3, p j x * fderiv ℝ φ x (EuclideanSpace.single j 1)) =
    ∫ x in Ω, (-(∑ j : Fin 3, pp j x)) * φ x
  calc
    _ = ∑ j : Fin 3, ∫ x in Ω, p j x * fderiv ℝ φ x (EuclideanSpace.single j 1) :=
      integral_finsetSum Finset.univ (fun j _ => hfirst j)
    _ = ∑ j : Fin 3, -(∫ x in Ω, pp j x * φ x) :=
      Finset.sum_congr rfl (fun j _ => hi j)
    _ = -(∑ j : Fin 3, ∫ x in Ω, pp j x * φ x) :=
      Finset.sum_neg_distrib (fun j : Fin 3 => ∫ x in Ω, pp j x * φ x)
    _ = -(∫ x in Ω, ∑ j : Fin 3, pp j x * φ x) :=
      congrArg Neg.neg (integral_finsetSum Finset.univ (fun j _ => hsecond j)).symm
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change -(∑ j : Fin 3, pp j x * φ x) = (-(∑ j : Fin 3, pp j x)) * φ x
        rw [neg_mul, Finset.sum_mul]

/-- The actual scalar C2 ODE supplies the same finite physical weak
equation on every open subdomain of the punctured unit ball. No assumed
weak equation or smoothness of the forcing is an input. -/
theorem native_finite_c2_physical_weak_equation
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩhalf : Ω ⊆ {x : E | x ≠ 0 ∧ ‖x‖ < 1})
    (V : ℝ → ℝ) (s : Finset AngularIndex) (q f : AngularIndex → ℝ → ℝ)
    (hq : ∀ i ∈ s, ContDiffOn ℝ 2 (q i) (Ioi 0))
    (heq : ∀ i ∈ s, ∀ t, 0 < t →
      deriv (deriv (q i)) t = (angularEigenvalue i + 1 / 4 - V t) * q i t + f i t) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ j : Fin 3,
        fderiv ℝ (finitePhysical s q) x (EuclideanSpace.single j 1) *
          fderiv ℝ φ x (EuclideanSpace.single j 1)) =
        ∫ x in Ω, (physicalForcing (finiteAngular s f) x / 8 +
          (V (-Real.log ‖x‖) / ‖x‖ ^ 2) * finitePhysical s q x) * φ x := by
  intro φ hφ hc hs
  have hu := (contDiffOn_finitePhysical_of_c2_positive s q hq).mono hΩhalf
  rw [native_C2_integral_gradient_eq_negative_trace hΩ hu hφ hc hs]
  apply setIntegral_congr_fun hΩ.measurableSet
  intro x hx
  dsimp only
  rw [native_finitePhysical_negative_trace_eq V s q f hq heq (hΩhalf hx).1 (hΩhalf hx).2]

#print axioms contDiffAt_cylinderLift_separable_of_c2
#print axioms contDiffOn_finitePhysical_of_c2_positive
#print axioms contDiffOn_projectedAngular_lift_of_c2_positive
#print axioms native_finitePhysical_trace_of_c2_at
#print axioms native_finitePhysical_negative_trace_eq
#print axioms native_finite_c2_physical_weak_equation

end Yamabe3.Analysis.SpherePolar
