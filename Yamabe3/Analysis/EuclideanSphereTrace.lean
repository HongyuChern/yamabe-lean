import Yamabe3.Analysis.ScaledIntervalTrace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Euclidean spherical value traces at the natural scale

All objects use the actual Euclidean metric and Lebesgue volume.  The
angular measure is Haar-to-sphere measure, with its proved polar Jacobian.
The final measure is the explicit radius-squared scaling of that angular
measure.  Transfer to the project's native round metric is a separate
proved measure-identity step.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace ENNReal

namespace Yamabe3.Analysis.EuclideanSphereTrace

abbrev E := EuclideanSpace ℝ (Fin 3)
abbrev S := sphere (0 : E) 1
abbrev angularVolume : Measure S := (volume : Measure E).toSphere

open Yamabe3.Analysis.SpherePolar

theorem measurePreserving_native_polar :
    MeasurePreserving (homeomorphUnitSphereProd E)
      ((volume : Measure E).comap (Subtype.val : ({(0 : E)}ᶜ : Set E) → E))
      (angularVolume.prod (Measure.volumeIoiPow 2)) := by
  simpa only [angularVolume, E, finrank_euclideanSpace, Fintype.card_fin,
    Nat.reduceSub] using (volume : Measure E).measurePreserving_homeomorphUnitSphereProd

theorem integrable_euclidean_iff_polar (f : E → ℝ) :
    Integrable f ↔ Integrable (fun p : S × Ioi (0 : ℝ) => f (p.2.1 • (p.1 : E)))
      (angularVolume.prod (Measure.volumeIoiPow 2)) := by
  have hinv (x : ({(0 : E)}ᶜ : Set E)) :
      (((homeomorphUnitSphereProd E) x).2 : ℝ) • (((homeomorphUnitSphereProd E) x).1 : E) = (x : E) := by
    simpa only [homeomorphUnitSphereProd_symm_apply_coe] using
      congrArg (fun y : ({(0 : E)}ᶜ : Set E) => (y : E))
        ((homeomorphUnitSphereProd E).symm_apply_apply x)
  have h := measurePreserving_native_polar.integrable_comp_emb
    (Homeomorph.measurableEmbedding _)
    (g := fun p => f ((homeomorphUnitSphereProd E).symm p))
  simp only [Function.comp_def, homeomorphUnitSphereProd_symm_apply_coe, hinv] at h
  rw [← restrict_compl_singleton (μ := (volume : Measure E)) 0,
    ← IntegrableOn, integrableOn_iff_comap_subtypeVal (isClosed_singleton.measurableSet.compl)]
  simpa only [Function.comp_def] using h

theorem integral_native_polar (f : E → ℝ) (hf : Integrable f) :
    (∫ x : E, f x) = ∫ θ : S, ∫ r : Ioi (0 : ℝ), f (r.1 • (θ : E))
      ∂Measure.volumeIoiPow 2 ∂angularVolume := by
  calc
    _ = ∫ x : ({(0 : E)}ᶜ : Set E), f x ∂((volume : Measure E).comap Subtype.val) := by
      rw [integral_subtype_comap (isClosed_singleton.measurableSet.compl),
        restrict_compl_singleton]
    _ = ∫ p : S × Ioi (0 : ℝ), f (p.2.1 • (p.1 : E))
        ∂(angularVolume.prod (Measure.volumeIoiPow 2)) := by
      simpa only [Homeomorph.symm_apply_apply, homeomorphUnitSphereProd_symm_apply_coe] using
        measurePreserving_native_polar.integral_comp (Homeomorph.measurableEmbedding _)
          (fun p => f ((homeomorphUnitSphereProd E).symm p))
    _ = _ := integral_prod _ ((integrable_euclidean_iff_polar f).mp hf)

theorem integral_radius_density (g : ℝ → ℝ) :
    (∫ r : Ioi (0 : ℝ), g r ∂Measure.volumeIoiPow 2) =
      ∫ r in Ioi (0 : ℝ), r ^ 2 * g r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
    ((measurable_subtype_coe.pow_const 2).real_toNNReal),
    integral_subtype_comap measurableSet_Ioi (fun r : ℝ => Real.toNNReal (r ^ 2) • g r)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  change Real.toNNReal (r ^ 2) • g r = r ^ 2 * g r
  rw [NNReal.smul_def, Real.coe_toNNReal _ (sq_nonneg r), smul_eq_mul]


def sphereTraceAnnulus (a b : ℝ) : Set E := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}

theorem isCompact_sphereTraceAnnulus (a b : ℝ) : IsCompact (sphereTraceAnnulus a b) := by
  apply (isCompact_closedBall (0 : E) b).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro x hx
    simpa only [mem_closedBall, dist_zero_right] using hx.2

theorem norm_sphereTrace_radial (θ : S) {r : ℝ} (hr : 0 ≤ r) :
    ‖r • (θ : E)‖ = r := by
  have hθ : ‖(θ : E)‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using θ.property
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hθ, mul_one]

theorem radial_mem_sphereTraceAnnulus {a b r : ℝ} (ha : 0 < a)
    (hr : r ∈ Icc a b) (θ : S) : r • (θ : E) ∈ sphereTraceAnnulus a b := by
  change a ≤ ‖r • (θ : E)‖ ∧ ‖r • (θ : E)‖ ≤ b
  rw [norm_sphereTrace_radial θ (ha.le.trans hr.1)]
  exact hr

/-- The radius-squared Jacobian and the native sphere measure are the
ones already proved from the genuine polar homeomorphism. -/
theorem integral_sphereTraceAnnulus_polar_fiber (f : E → ℝ) {a b : ℝ}
    (ha : 0 < a) (θ : S) :
    (∫ r : Ioi (0 : ℝ), (sphereTraceAnnulus a b).indicator f (r.1 • (θ : E))
      ∂Measure.volumeIoiPow 2) = ∫ r in Icc a b, r ^ 2 * f (r • (θ : E)) := by
  rw [integral_radius_density
    (fun t : ℝ => (sphereTraceAnnulus a b).indicator f (t • (θ : E)))]
  calc
    _ = ∫ r in Ioi (0 : ℝ), (Icc a b).indicator
        (fun t => t ^ 2 * f (t • (θ : E))) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hm : r • (θ : E) ∈ sphereTraceAnnulus a b ↔ r ∈ Icc a b := by
        change (a ≤ ‖r • (θ : E)‖ ∧ ‖r • (θ : E)‖ ≤ b) ↔ _
        rw [norm_sphereTrace_radial θ hr.le]
        rfl
      change r ^ 2 * (sphereTraceAnnulus a b).indicator f (r • (θ : E)) =
        (Icc a b).indicator (fun t => t ^ 2 * f (t • (θ : E))) r
      by_cases h : r ∈ Icc a b
      · rw [indicator_of_mem h, indicator_of_mem (hm.mpr h)]
      · rw [indicator_of_notMem h, indicator_of_notMem (fun hx => h (hm.mp hx)), mul_zero]
    _ = _ := by
      rw [setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr
        (show Icc a b ⊆ Ioi (0 : ℝ) from fun r hr => ha.trans_le hr.1)]

theorem integral_sphereTraceAnnulus_native_polar {f : E → ℝ} {a b : ℝ}
    (ha : 0 < a) (hf : IntegrableOn f (sphereTraceAnnulus a b)) :
    (∫ x in sphereTraceAnnulus a b, f x) =
      ∫ θ : S, (∫ r : ℝ in Icc a b, r ^ 2 * f (r • (θ : E))) ∂angularVolume := by
  have hK := (isCompact_sphereTraceAnnulus a b).measurableSet
  have hi : Integrable ((sphereTraceAnnulus a b).indicator f) :=
    (integrable_indicator_iff hK).mpr hf
  calc
    _ = ∫ x : E, (sphereTraceAnnulus a b).indicator f x := (integral_indicator hK).symm
    _ = ∫ θ : S, ∫ r : Ioi (0 : ℝ),
        (sphereTraceAnnulus a b).indicator f (r.1 • (θ : E))
          ∂Measure.volumeIoiPow 2 ∂angularVolume := integral_native_polar _ hi
    _ = _ := by simp_rw [integral_sphereTraceAnnulus_polar_fiber f ha]

theorem integrable_sphereTraceAnnulus_polar_fiber {f : E → ℝ} {a b : ℝ}
    (ha : 0 < a) (hf : IntegrableOn f (sphereTraceAnnulus a b)) :
    Integrable (fun θ : S => ∫ r in Icc a b, r ^ 2 * f (r • (θ : E))) angularVolume := by
  have hK := (isCompact_sphereTraceAnnulus a b).measurableSet
  have hi : Integrable ((sphereTraceAnnulus a b).indicator f) :=
    (integrable_indicator_iff hK).mpr hf
  have hp := ((integrable_euclidean_iff_polar _).mp hi).integral_prod_left
  change Integrable (fun θ : S => ∫ r : Ioi (0 : ℝ),
    (sphereTraceAnnulus a b).indicator f (r.1 • (θ : E))
      ∂Measure.volumeIoiPow 2) angularVolume at hp
  simpa only [integral_sphereTraceAnnulus_polar_fiber f ha] using hp


def scaledSphereTraceEnergy (L : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  f x ^ 2 + L ^ 2 * ‖fderiv ℝ f x‖ ^ 2

/-- The value integral uses the actual round angular measure.  The interval
length is retained in the derivative energy before any radius is fixed. -/
theorem integral_sphere_restriction_sq_le_scaled_annulus_energy {a b r : ℝ}
    (ha : 0 < a) (hab : a < b) (hr : r ∈ Icc a b)
    {O : Set E} (hO : IsOpen O) (hKO : sphereTraceAnnulus a b ⊆ O)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) :
    (∫ θ : S, f (r • (θ : E)) ^ 2 ∂angularVolume) ≤
      (2 / ((b - a) * a ^ 2)) *
        ∫ x in sphereTraceAnnulus a b, scaledSphereTraceEnergy (b - a) f x := by
  have hL : 0 < b - a := sub_pos.mpr hab
  have hfc := hf.continuousOn
  have hdc : ContinuousOn (fderiv ℝ f) O :=
    hf.continuousOn_fderiv_of_isOpen hO (by simp)
  have hEc : ContinuousOn (scaledSphereTraceEnergy (b - a) f) O :=
    (hfc.pow 2).add (continuousOn_const.mul (hdc.norm.pow 2))
  have hEi : IntegrableOn (scaledSphereTraceEnergy (b - a) f) (sphereTraceAnnulus a b) :=
    (hEc.mono hKO).integrableOn_compact (isCompact_sphereTraceAnnulus a b)
  have hmap (θ : S) : MapsTo (fun t : ℝ => t • (θ : E)) (Icc a b) O :=
    fun t ht => hKO (radial_mem_sphereTraceAnnulus ha ht θ)
  have htrace : Continuous (fun θ : S => f (r • (θ : E))) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hc : ContinuousAt (fun q : S => r • (q : E)) θ :=
      by simpa only [Pi.smul_apply] using!
        ((continuous_const : Continuous (fun _ : S => r)).smul
          (continuous_subtype_val : Continuous (Subtype.val : S → E))).continuousAt (x := θ)
    exact ContinuousAt.comp (f := fun q : S => r • (q : E))
      (hfc.continuousAt (hO.mem_nhds (hmap θ hr))) hc
  have hti : Integrable (fun θ : S => f (r • (θ : E)) ^ 2) angularVolume := by
    simpa only [integrableOn_univ, Pi.pow_apply] using!
      (htrace.pow 2).continuousOn.integrableOn_compact
        (μ := angularVolume) (isCompact_univ : IsCompact (univ : Set S))
  have hbound (θ : S) : f (r • (θ : E)) ^ 2 ≤
      (2 / ((b - a) * a ^ 2)) *
        ∫ t in Icc a b, t ^ 2 * scaledSphereTraceEnergy (b - a) f (t • (θ : E)) := by
    let F : ℝ → ℝ := fun t => f (t • (θ : E))
    let D : ℝ → ℝ := fun t => fderiv ℝ f (t • (θ : E)) (θ : E)
    have hlin : Continuous (fun t : ℝ => t • (θ : E)) := continuous_id.smul continuous_const
    have hF : ContinuousOn F (Icc a b) := hfc.comp hlin.continuousOn (hmap θ)
    have hD : ContinuousOn D (Icc a b) :=
      (hdc.comp hlin.continuousOn (hmap θ)).clm_apply continuousOn_const
    have hFD (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt F (D t) t := by
      have h := (hf.contDiffAt (hO.mem_nhds (hmap θ ht))).differentiableAt (by simp)
      simpa only [F, D, Function.comp_def, one_smul] using!
        h.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const (θ : E))
    have htheta : ‖(θ : E)‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using θ.property
    have hpoint (t : ℝ) (ht : t ∈ Icc a b) :
        a ^ 2 * (F t ^ 2 + (b - a) ^ 2 * D t ^ 2) ≤
          t ^ 2 * scaledSphereTraceEnergy (b - a) f (t • (θ : E)) := by
      have hd := (fderiv ℝ f (t • (θ : E))).le_opNorm (θ : E)
      rw [htheta, mul_one, Real.norm_eq_abs] at hd
      have hds : D t ^ 2 ≤ ‖fderiv ℝ f (t • (θ : E))‖ ^ 2 := by
        have hs := (sq_le_sq₀ (abs_nonneg _) (ContinuousLinearMap.opNorm_nonneg _)).mpr hd
        simpa only [D, sq_abs] using hs
      have hat : a ^ 2 ≤ t ^ 2 := (sq_le_sq₀ ha.le (ha.le.trans ht.1)).mpr ht.1
      exact mul_le_mul hat
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hds (sq_nonneg _)))
        (add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))) (sq_nonneg _)
    have hFDi : IntegrableOn (fun t => F t ^ 2 + (b - a) ^ 2 * D t ^ 2) (Icc a b) :=
      ((hF.pow 2).add (continuousOn_const.mul (hD.pow 2))).integrableOn_compact isCompact_Icc
    have hEiθ : IntegrableOn (fun t =>
        t ^ 2 * scaledSphereTraceEnergy (b - a) f (t • (θ : E))) (Icc a b) :=
      ((continuousOn_id.pow 2).mul (hEc.comp hlin.continuousOn (hmap θ))).integrableOn_compact
        isCompact_Icc
    have hweighted : a ^ 2 * (∫ t in Icc a b, F t ^ 2 + (b - a) ^ 2 * D t ^ 2) ≤
        ∫ t in Icc a b, t ^ 2 * scaledSphereTraceEnergy (b - a) f (t • (θ : E)) := by
      rw [← integral_const_mul]
      exact setIntegral_mono_on (hFDi.const_mul _) hEiθ measurableSet_Icc hpoint
    have hdiv : (∫ t in Icc a b, F t ^ 2 + (b - a) ^ 2 * D t ^ 2) ≤
        (∫ t in Icc a b, t ^ 2 * scaledSphereTraceEnergy (b - a) f (t • (θ : E))) /
          a ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
      simpa only [mul_comm] using hweighted
    calc
      _ ≤ (2 / (b - a)) * ∫ t in Icc a b, F t ^ 2 + (b - a) ^ 2 * D t ^ 2 :=
        sq_apply_le_scaled_interval_energy hab hr hF hD hFD
      _ ≤ (2 / (b - a)) *
          ((∫ t in Icc a b, t ^ 2 * scaledSphereTraceEnergy (b - a) f (t • (θ : E))) /
            a ^ 2) := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = _ := by field_simp [hL.ne', ha.ne']; <;> ring
  have hJi := integrable_sphereTraceAnnulus_polar_fiber ha hEi
  calc
    _ ≤ ∫ θ : S, (2 / ((b - a) * a ^ 2)) *
        (∫ t in Icc a b, t ^ 2 * scaledSphereTraceEnergy (b - a) f (t • (θ : E)))
          ∂angularVolume := integral_mono hti (hJi.const_mul _) hbound
    _ = _ := by
      rw [integral_const_mul, ← integral_sphereTraceAnnulus_native_polar ha hEi]

/-- On the annulus with radii r/2 and 3r/2, use the physical area r² dω.
The universal constant eight precedes the positive radius and the function. -/
theorem integral_physical_sphere_restriction_sq_le_scaled_energy
    {r : ℝ} (hr : 0 < r) {O : Set E} (hO : IsOpen O)
    (hKO : sphereTraceAnnulus (r / 2) (3 * r / 2) ⊆ O)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) :
    (∫ θ : S, f (r • (θ : E)) ^ 2
      ∂((ENNReal.ofReal (r ^ 2)) • angularVolume)) ≤
      (8 / r) * ∫ x in sphereTraceAnnulus (r / 2) (3 * r / 2),
        f x ^ 2 + r ^ 2 * ‖fderiv ℝ f x‖ ^ 2 := by
  have ha : 0 < r / 2 := by positivity
  have hab : r / 2 < 3 * r / 2 := by linarith only [hr]
  have hrab : r ∈ Icc (r / 2) (3 * r / 2) := by
    constructor <;> linarith only [hr]
  have hL : 3 * r / 2 - r / 2 = r := by ring
  have h := integral_sphere_restriction_sq_le_scaled_annulus_energy ha hab hrab hO hKO hf
  have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg r)
  rw [integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg r), smul_eq_mul]
  have hc : r ^ 2 * (2 / (r * (r / 2) ^ 2)) = 8 / r := by
    field_simp [hr.ne']
    <;> ring
  simpa only [hL, ← mul_assoc, hc, scaledSphereTraceEnergy] using hmul


#print axioms integral_sphere_restriction_sq_le_scaled_annulus_energy
#print axioms integral_physical_sphere_restriction_sq_le_scaled_energy

end Yamabe3.Analysis.EuclideanSphereTrace
