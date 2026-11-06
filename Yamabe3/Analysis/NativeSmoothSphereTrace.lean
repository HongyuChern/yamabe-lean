import Yamabe3.Analysis.Cylinder.NativePolarMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A genuine fixed-radius sphere value estimate

The one-dimensional fundamental theorem applied to f squared, together
with the elementary Cauchy--Schwarz/Young bound |2 f f'| <= f^2 + f'^2,
controls an actual value on a compact interval. The actual native polar
formula, including its radius-squared Jacobian, then bounds the native
round-sphere L2 restriction of a smooth function by its ordinary energy
on a compact annulus. No trace estimate is an input.

The second module applies this estimate to true smooth metric charts and
extends the actual restriction map to the native energy completion.
This source has not yet been compiled.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

/-- A true one-dimensional value estimate. The derivative witness is an
ordinary pointwise derivative on the entire closed interval. -/
theorem sq_apply_le_interval_energy {a b r : ℝ} (hab : a < b)
    (hr : r ∈ Icc a b) {f df : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn df (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (df t) t) :
    f r ^ 2 ≤ ((b - a)⁻¹ + 1) * ∫ t in Icc a b, f t ^ 2 + df t ^ 2 := by
  let q : ℝ → ℝ := fun t => f t ^ 2 + df t ^ 2
  let d : ℝ → ℝ := fun t => 2 * f t * df t
  have hqc : ContinuousOn q (Icc a b) := (hf.pow 2).add (hdf.pow 2)
  have hdc : ContinuousOn d (Icc a b) := (continuousOn_const.mul hf).mul hdf
  have hqi : IntegrableOn q (Icc a b) := hqc.integrableOn_compact isCompact_Icc
  have hdi : IntegrableOn (fun t => ‖d t‖) (Icc a b) :=
    hdc.norm.integrableOn_compact isCompact_Icc
  have hdq (t : ℝ) : ‖d t‖ ≤ q t := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    dsimp only [d, q]
    constructor
    · nlinarith only [sq_nonneg (f t + df t)]
    · nlinarith only [sq_nonneg (f t - df t)]
  have hpoint (s : ℝ) (hs : s ∈ Icc a b) :
      f r ^ 2 ≤ f s ^ 2 + ∫ t in Icc a b, q t := by
    have hsub : uIcc s r ⊆ Icc a b := by
      intro t ht
      exact ⟨(le_min hs.1 hr.1).trans ht.1, ht.2.trans (max_le hs.2 hr.2)⟩
    have hftc : (∫ t in s..r, d t) = f r ^ 2 - f s ^ 2 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t : ℝ => f t ^ 2) (f' := d)
      · intro t ht
        simpa only [d, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply] using!
          (hd t (hsub ht)).pow 2
      · exact (hdc.mono hsub).intervalIntegrable
    have hnorm : |f r ^ 2 - f s ^ 2| ≤ ∫ t in Icc a b, q t := by
      calc
        _ = ‖∫ t in s..r, d t‖ := by rw [hftc, Real.norm_eq_abs]
        _ ≤ ∫ t in uIoc s r, ‖d t‖ :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
        _ ≤ ∫ t in Icc a b, ‖d t‖ :=
          setIntegral_mono_set hdi (Eventually.of_forall fun _ => norm_nonneg _)
            (Eventually.of_forall fun t ht => hsub (uIoc_subset_uIcc ht))
        _ ≤ ∫ t in Icc a b, q t :=
          setIntegral_mono_on hdi hqi measurableSet_Icc (fun t _ => hdq t)
    have hle := (le_abs_self (f r ^ 2 - f s ^ 2)).trans hnorm
    linarith only [hle]
  have hfi : IntegrableOn (fun s => f s ^ 2) (Icc a b) :=
    (hf.pow 2).integrableOn_compact isCompact_Icc
  have hconst : IntegrableOn (fun _ : ℝ => ∫ t in Icc a b, q t) (Icc a b) :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ => ∫ t in Icc a b, q t)
      (Icc a b)).integrableOn_compact isCompact_Icc
  have havg : (b - a) * f r ^ 2 ≤
      (∫ s in Icc a b, f s ^ 2) + (b - a) * ∫ t in Icc a b, q t := by
    have hi := setIntegral_mono_on
      ((continuousOn_const : ContinuousOn (fun _ : ℝ => f r ^ 2)
        (Icc a b)).integrableOn_compact isCompact_Icc)
      (hfi.add hconst) measurableSet_Icc hpoint
    simpa only [integral_add' hfi hconst, integral_const, measureReal_restrict_apply_univ,
      smul_eq_mul, Real.volume_real_Icc_of_le hab.le] using hi
  have hfle : (∫ s in Icc a b, f s ^ 2) ≤ ∫ t in Icc a b, q t := by
    apply setIntegral_mono_on hfi hqi measurableSet_Icc
    intro t _
    exact le_add_of_nonneg_right (sq_nonneg (df t))
  apply le_of_mul_le_mul_left (a := b - a) _ (sub_pos.mpr hab)
  have hcancel : (b - a) * (((b - a)⁻¹ + 1) * ∫ t in Icc a b, q t) =
      (∫ t in Icc a b, q t) + (b - a) * ∫ t in Icc a b, q t := by
    field_simp [(sub_pos.mpr hab).ne']
    <;> ring
  change (b - a) * f r ^ 2 ≤ (b - a) * (((b - a)⁻¹ + 1) * ∫ t in Icc a b, q t)
  rw [hcancel]
  exact havg.trans (add_le_add hfle le_rfl)

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

def sphereTraceEnergyDensity (f : E → ℝ) (x : E) : ℝ :=
  f x ^ 2 + ‖fderiv ℝ f x‖ ^ 2

theorem sphereTraceEnergyDensity_nonneg (f : E → ℝ) (x : E) :
    0 ≤ sphereTraceEnergyDensity f x := add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The actual native sphere restriction of a smooth function is controlled
by its Euclidean coordinate energy on the actual compact annulus. -/
theorem integral_sphere_restriction_sq_le_annulus_energy {a b r : ℝ}
    (ha : 0 < a) (hab : a < b) (hr : r ∈ Icc a b)
    {O : Set E} (hO : IsOpen O) (hKO : sphereTraceAnnulus a b ⊆ O)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) :
    (∫ θ : S, f (r • (θ : E)) ^ 2 ∂angularVolume) ≤
      (((b - a)⁻¹ + 1) / a ^ 2) *
        ∫ x in sphereTraceAnnulus a b, sphereTraceEnergyDensity f x := by
  have hfc := hf.continuousOn
  have hdc : ContinuousOn (fderiv ℝ f) O :=
    hf.continuousOn_fderiv_of_isOpen hO (by simp)
  have hEc : ContinuousOn (sphereTraceEnergyDensity f) O :=
    (hfc.pow 2).add (hdc.norm.pow 2)
  have hEi : IntegrableOn (sphereTraceEnergyDensity f) (sphereTraceAnnulus a b) :=
    (hEc.mono hKO).integrableOn_compact (isCompact_sphereTraceAnnulus a b)
  have hmap (θ : S) : MapsTo (fun t : ℝ => t • (θ : E)) (Icc a b) O :=
    fun t ht => hKO (radial_mem_sphereTraceAnnulus ha ht θ)
  have htrace : Continuous (fun θ : S => f (r • (θ : E))) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hc : ContinuousAt (fun q : S => r • (q : E)) θ := by
      simpa only [Pi.smul_apply] using!
        ((continuous_const : Continuous (fun _ : S => r)).smul
          (continuous_subtype_val : Continuous (Subtype.val : S → E))).continuousAt (x := θ)
    exact ContinuousAt.comp (f := fun q : S => r • (q : E))
      (hfc.continuousAt (hO.mem_nhds (hmap θ hr))) hc
  have hti : Integrable (fun θ : S => f (r • (θ : E)) ^ 2) angularVolume := by
    simpa only [integrableOn_univ, Pi.pow_apply] using!
      (htrace.pow 2).continuousOn.integrableOn_compact
        (μ := angularVolume) (isCompact_univ : IsCompact (univ : Set S))
  have hci : 0 ≤ ((b - a)⁻¹ + 1) / a ^ 2 := by positivity
  have hbound (θ : S) : f (r • (θ : E)) ^ 2 ≤
      (((b - a)⁻¹ + 1) / a ^ 2) *
        ∫ t in Icc a b, t ^ 2 * sphereTraceEnergyDensity f (t • (θ : E)) := by
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
        a ^ 2 * (F t ^ 2 + D t ^ 2) ≤
          t ^ 2 * sphereTraceEnergyDensity f (t • (θ : E)) := by
      have hd := (fderiv ℝ f (t • (θ : E))).le_opNorm (θ : E)
      rw [htheta, mul_one, Real.norm_eq_abs] at hd
      have hds : D t ^ 2 ≤ ‖fderiv ℝ f (t • (θ : E))‖ ^ 2 := by
        have hs := (sq_le_sq₀ (abs_nonneg _) (ContinuousLinearMap.opNorm_nonneg _)).mpr hd
        simpa only [D, sq_abs] using hs
      have hat : a ^ 2 ≤ t ^ 2 := (sq_le_sq₀ ha.le (ha.le.trans ht.1)).mpr ht.1
      exact mul_le_mul hat (add_le_add le_rfl hds) (add_nonneg (sq_nonneg _) (sq_nonneg _))
        (sq_nonneg _)
    have hFDi : IntegrableOn (fun t => F t ^ 2 + D t ^ 2) (Icc a b) :=
      ((hF.pow 2).add (hD.pow 2)).integrableOn_compact isCompact_Icc
    have hEiθ : IntegrableOn (fun t => t ^ 2 * sphereTraceEnergyDensity f (t • (θ : E)))
        (Icc a b) :=
      ((continuousOn_id.pow 2).mul (hEc.comp hlin.continuousOn (hmap θ))).integrableOn_compact
        isCompact_Icc
    have hweighted : a ^ 2 * (∫ t in Icc a b, F t ^ 2 + D t ^ 2) ≤
        ∫ t in Icc a b, t ^ 2 * sphereTraceEnergyDensity f (t • (θ : E)) := by
      rw [← integral_const_mul]
      exact setIntegral_mono_on (hFDi.const_mul _) hEiθ measurableSet_Icc hpoint
    have hdiv : (∫ t in Icc a b, F t ^ 2 + D t ^ 2) ≤
        (∫ t in Icc a b, t ^ 2 * sphereTraceEnergyDensity f (t • (θ : E))) / a ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
      simpa only [mul_comm] using hweighted
    calc
      _ ≤ ((b - a)⁻¹ + 1) * ∫ t in Icc a b, F t ^ 2 + D t ^ 2 :=
        sq_apply_le_interval_energy hab hr hF hD hFD
      _ ≤ ((b - a)⁻¹ + 1) *
          ((∫ t in Icc a b, t ^ 2 * sphereTraceEnergyDensity f (t • (θ : E))) / a ^ 2) :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = _ := by ring
  have hJi := integrable_sphereTraceAnnulus_polar_fiber ha hEi
  calc
    _ ≤ ∫ θ : S, (((b - a)⁻¹ + 1) / a ^ 2) *
        (∫ t in Icc a b, t ^ 2 * sphereTraceEnergyDensity f (t • (θ : E)))
          ∂angularVolume := integral_mono hti (hJi.const_mul _) hbound
    _ = _ := by
      rw [integral_const_mul, ← integral_sphereTraceAnnulus_native_polar ha hEi]

#print axioms sq_apply_le_interval_energy
#print axioms integral_sphereTraceAnnulus_native_polar
#print axioms integral_sphere_restriction_sq_le_annulus_energy

end Yamabe3.Analysis.SpherePolar
