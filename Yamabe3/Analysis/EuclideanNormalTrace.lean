import Yamabe3.Analysis.EuclideanSphereTrace
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# The actual Euclidean normal derivative at the natural H2 scale

The normal derivative is `Df(r θ) θ`, on the same function whose value
trace is estimated in EuclideanSphereTrace.  Coordinate derivatives are
derived from the true Frechet derivative and the Euclidean orthonormal
basis.  This file does not identify a general-metric weak conormal with
this Euclidean normal derivative.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace ENNReal BigOperators

namespace Yamabe3.Analysis.EuclideanSphereTrace

theorem continuous_restriction_to_sphere {F : Type*} [TopologicalSpace F]
    {O : Set E} (hO : IsOpen O) {f : E → F} (hf : ContinuousOn f O)
    (r : ℝ) (hs : ∀ θ : S, r • (θ : E) ∈ O) :
    Continuous (fun θ : S => f (r • (θ : E))) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hc : ContinuousAt (fun q : S => r • (q : E)) θ := by
    simpa only [Pi.smul_apply] using!
      ((continuous_const : Continuous (fun _ : S => r)).smul
        (continuous_subtype_val : Continuous (Subtype.val : S → E))).continuousAt (x := θ)
  exact ContinuousAt.comp (f := fun q : S => r • (q : E))
    (hf.continuousAt (hO.mem_nhds (hs θ))) hc

def coordinateDerivative (f : E → ℝ) (i : Fin 3) (x : E) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i)

theorem contDiffOn_coordinateDerivative {O : Set E} (hO : IsOpen O)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (i : Fin 3) :
    ContDiffOn ℝ ∞ (coordinateDerivative f i) O :=
  (hf.fderiv_of_isOpen (m := ∞) hO (by simp)).clm_apply contDiffOn_const

theorem coordinateDerivative_norm_le (f : E → ℝ) (i : Fin 3) (x : E) :
    ‖coordinateDerivative f i x‖ ≤ ‖fderiv ℝ f x‖ := by
  simpa only [coordinateDerivative, (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one, mul_one]
    using (fderiv ℝ f x).le_opNorm (EuclideanSpace.basisFun (Fin 3) ℝ i)

theorem fderiv_coordinateDerivative_norm_le {O : Set E} (hO : IsOpen O)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (i : Fin 3) {x : E} (hx : x ∈ O) :
    ‖fderiv ℝ (coordinateDerivative f i) x‖ ≤ ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  have hc : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_of_isOpen (m := ∞) hO (by simp)).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have heq := (hc.hasFDerivAt.clm_apply
    (hasFDerivAt_const (EuclideanSpace.basisFun (Fin 3) ℝ i) x)).fderiv
  change fderiv ℝ (coordinateDerivative f i) x = _ at heq
  simp only [ContinuousLinearMap.comp_zero, zero_add] at heq
  rw [heq]
  simpa only [ContinuousLinearMap.opNorm_flip,
    (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one, mul_one] using
    (fderiv ℝ (fderiv ℝ f) x).flip.le_opNorm (EuclideanSpace.basisFun (Fin 3) ℝ i)

theorem linear_apply_sq_le_sum_coordinates (A : E →L[ℝ] ℝ) (θ : S) :
    (A (θ : E)) ^ 2 ≤ ∑ i : Fin 3, (A (EuclideanSpace.basisFun (Fin 3) ℝ i)) ^ 2 := by
  have hrepr : A (θ : E) =
      ∑ i : Fin 3, (θ : E) i * A (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (θ : E)]
    simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr, smul_eq_mul]
  have hθ : ‖(θ : E)‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using θ.property
  have hnorm : (∑ i : Fin 3, ((θ : E) i) ^ 2) = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hθ, one_pow]
  rw [hrepr]
  simpa only [hnorm, one_mul] using Finset.sum_mul_sq_le_sq_mul_sq
    Finset.univ (fun i : Fin 3 => (θ : E) i)
    (fun i : Fin 3 => A (EuclideanSpace.basisFun (Fin 3) ℝ i))

theorem integral_physical_sphere_normal_sq_le_scaled_hessian_energy
    {r : ℝ} (hr : 0 < r) {O : Set E} (hO : IsOpen O)
    (hKO : sphereTraceAnnulus (r / 2) (3 * r / 2) ⊆ O)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) :
    (∫ θ : S, (fderiv ℝ f (r • (θ : E)) (θ : E)) ^ 2
      ∂((ENNReal.ofReal (r ^ 2)) • angularVolume)) ≤
      (24 / r) * ∫ x in sphereTraceAnnulus (r / 2) (3 * r / 2),
        ‖fderiv ℝ f x‖ ^ 2 + r ^ 2 * ‖fderiv ℝ (fderiv ℝ f) x‖ ^ 2 := by
  let K := sphereTraceAnnulus (r / 2) (3 * r / 2)
  let Q : E → ℝ := fun x =>
    ‖fderiv ℝ f x‖ ^ 2 + r ^ 2 * ‖fderiv ℝ (fderiv ℝ f) x‖ ^ 2
  have ha : 0 < r / 2 := by positivity
  have hrab : r ∈ Icc (r / 2) (3 * r / 2) := by constructor <;> linarith only [hr]
  have hs (θ : S) : r • (θ : E) ∈ O :=
    hKO (radial_mem_sphereTraceAnnulus ha hrab θ)
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ f) O := hf.fderiv_of_isOpen (m := ∞) hO (by simp)
  have hDD : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ f)) O := hD.fderiv_of_isOpen (m := ∞) hO (by simp)
  have hDn : ContinuousOn (fun x : E => ‖fderiv ℝ f x‖) O :=
    (continuous_norm : Continuous (fun A : E →L[ℝ] ℝ => ‖A‖)).comp_continuousOn hD.continuousOn
  have hDDn : ContinuousOn (fun x : E => ‖fderiv ℝ (fderiv ℝ f) x‖) O :=
    (continuous_norm (E := E →L[ℝ] E →L[ℝ] ℝ)).comp_continuousOn
      hDD.continuousOn
  have hQc : ContinuousOn Q O := by
    simpa only [Q, Pi.pow_apply, Pi.mul_apply, Pi.add_apply] using!
      (hDn.pow 2).add
        ((continuousOn_const : ContinuousOn (fun _ : E => r ^ 2) O).mul
          (hDDn.pow 2))
  have hQi : IntegrableOn Q K :=
    (hQc.mono hKO).integrableOn_compact (isCompact_sphereTraceAnnulus _ _)
  have hdc := continuous_restriction_to_sphere hO hD.continuousOn r hs
  have hnc : Continuous (fun θ : S => fderiv ℝ f (r • (θ : E)) (θ : E)) :=
    hdc.clm_apply continuous_subtype_val
  have hni : Integrable (fun θ : S => (fderiv ℝ f (r • (θ : E)) (θ : E)) ^ 2)
      angularVolume := by
    simpa only [integrableOn_univ, Pi.pow_apply] using!
      (hnc.pow 2).continuousOn.integrableOn_compact
        (μ := angularVolume) (isCompact_univ : IsCompact (univ : Set S))
  have hci (i : Fin 3) : Integrable (fun θ : S => coordinateDerivative f i (r • (θ : E)) ^ 2)
      angularVolume := by
    have hc := continuous_restriction_to_sphere hO
      (contDiffOn_coordinateDerivative hO hf i).continuousOn r hs
    simpa only [integrableOn_univ, Pi.pow_apply] using!
      (hc.pow 2).continuousOn.integrableOn_compact
        (μ := angularVolume) (isCompact_univ : IsCompact (univ : Set S))
  have hiBound (i : Fin 3) :
      r ^ 2 * (∫ θ : S, coordinateDerivative f i (r • (θ : E)) ^ 2 ∂angularVolume) ≤
        (8 / r) * ∫ x in K, Q x := by
    have hciSmooth := contDiffOn_coordinateDerivative hO hf i
    have hfirst := integral_physical_sphere_restriction_sq_le_scaled_energy hr hO hKO hciSmooth
    rw [integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg r), smul_eq_mul] at hfirst
    have hFdc : ContinuousOn (fun x : E => ‖fderiv ℝ (coordinateDerivative f i) x‖) O :=
      (continuous_norm : Continuous (fun A : E →L[ℝ] ℝ => ‖A‖)).comp_continuousOn
        (hciSmooth.continuousOn_fderiv_of_isOpen hO (by simp))
    have hFFc : ContinuousOn (fun x => coordinateDerivative f i x ^ 2 +
        r ^ 2 * ‖fderiv ℝ (coordinateDerivative f i) x‖ ^ 2) O := by
      simpa only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply] using!
        (hciSmooth.continuousOn.pow 2).add
          ((continuousOn_const : ContinuousOn (fun _ : E => r ^ 2) O).mul (hFdc.pow 2))
    have hfirstIntegrable : IntegrableOn (fun x => coordinateDerivative f i x ^ 2 +
        r ^ 2 * ‖fderiv ℝ (coordinateDerivative f i) x‖ ^ 2) K :=
      (hFFc.mono hKO).integrableOn_compact (isCompact_sphereTraceAnnulus _ _)
    apply hfirst.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply setIntegral_mono_on hfirstIntegrable hQi
      (isCompact_sphereTraceAnnulus _ _).measurableSet
    intro x hx
    have h0 : coordinateDerivative f i x ^ 2 ≤ ‖fderiv ℝ f x‖ ^ 2 := by
      have h := (sq_le_sq₀ (norm_nonneg (coordinateDerivative f i x))
        (ContinuousLinearMap.opNorm_nonneg (fderiv ℝ f x))).mpr (coordinateDerivative_norm_le f i x)
      simpa only [Real.norm_eq_abs, sq_abs] using h
    have h1 : ‖fderiv ℝ (coordinateDerivative f i) x‖ ^ 2 ≤
        ‖fderiv ℝ (fderiv ℝ f) x‖ ^ 2 :=
      (sq_le_sq₀ (ContinuousLinearMap.opNorm_nonneg _)
        (ContinuousLinearMap.opNorm_nonneg _)).mpr
        (fderiv_coordinateDerivative_norm_le hO hf i (hKO hx))
    simpa only [Q] using
      add_le_add h0 (mul_le_mul_of_nonneg_left h1 (sq_nonneg r))
  rw [integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg r), smul_eq_mul]
  calc
    _ ≤ r ^ 2 * (∫ θ : S, ∑ i : Fin 3,
        coordinateDerivative f i (r • (θ : E)) ^ 2 ∂angularVolume) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
      apply integral_mono hni (integrable_finsetSum _ (fun i _ => hci i))
      intro θ
      exact linear_apply_sq_le_sum_coordinates (fderiv ℝ f (r • (θ : E))) θ
    _ = ∑ i : Fin 3, r ^ 2 *
        (∫ θ : S, coordinateDerivative f i (r • (θ : E)) ^ 2 ∂angularVolume) := by
      rw [integral_finsetSum _ (fun i _ => hci i), Finset.mul_sum]
    _ ≤ ∑ _i : Fin 3, (8 / r) * ∫ x in K, Q x :=
      Finset.sum_le_sum fun i _ => hiBound i
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

#print axioms integral_physical_sphere_normal_sq_le_scaled_hessian_energy

end Yamabe3.Analysis.EuclideanSphereTrace
