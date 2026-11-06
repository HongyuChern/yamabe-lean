import Yamabe3.Analysis.EuclideanSphereTrace

/-! The actual spherical trace estimate requires only C1 regularity.
This project proof adapts the earlier smooth proof without modifying it. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace ENNReal
namespace Yamabe3.Analysis.EuclideanSphereTrace
open Yamabe3.Analysis.SpherePolar

theorem integral_sphere_restriction_sq_le_scaled_annulus_energy_C1 {a b r : ℝ}
    (ha : 0 < a) (hab : a < b) (hr : r ∈ Icc a b)
    {O : Set E} (hO : IsOpen O) (hKO : sphereTraceAnnulus a b ⊆ O)
    {f : E → ℝ} (hf : ContDiffOn ℝ 1 f O) :
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


#print axioms integral_sphere_restriction_sq_le_scaled_annulus_energy_C1
end Yamabe3.Analysis.EuclideanSphereTrace
